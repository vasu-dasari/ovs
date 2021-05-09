/* Copyright (c) 2013, 2014, 2015, 2017 Nicira, Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at:
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License. */

#include <config.h>
#include <errno.h>

#include "byte-order.h"
#include "connectivity.h"
#include "csum.h"
#include "dpif.h"
#include "openvswitch/dynamic-string.h"
#include "fat-rwlock.h"
#include "hash.h"
#include "openvswitch/hmap.h"
#include "netdev.h"
#include "odp-util.h"
#include "openvswitch/ofpbuf.h"
#include "packets.h"
#include "route-table.h"
#include "seq.h"
#include "smap.h"
#include "socket-util.h"
#include "tnl-ports.h"
#include "tunnel.h"
#include "openvswitch/vlog.h"
#include "unaligned.h"
#include "unixctl.h"
#include "ofproto-dpif.h"
#include "ofproto-dpif-xlate.h"
#include "netdev-vport.h"

VLOG_DEFINE_THIS_MODULE(tunnel);

struct tnl_match {
    ovs_be64 in_key;
    struct in6_addr ipv6_src;
    struct in6_addr ipv6_dst;
    odp_port_t odp_port;
    bool in_key_flow;
    bool ip_src_flow;
    bool ip_dst_flow;
    bool dl_port_flow;
    bool vlan_id_flow;
    ovs_be32 dl_odp_port;
    ovs_be16 vlan_id;
    enum netdev_pt_mode pt_mode;
};

struct tnl_port {
    struct hmap_node ofport_node;
    struct hmap_node match_node;

    const struct ofport_dpif *ofport;
    uint64_t change_seq;
    struct netdev *netdev;

    struct tnl_match match;
    ovs_be32 dl_ofp_port;
};

struct tnl_smac_entry {
    struct eth_addr mac;
    uint16_t vlan;
    size_t ref_cnt;
    struct hmap_node node;
};

static struct fat_rwlock rwlock;

/* Tunnel matches.
 *
 * This module maps packets received over tunnel protocols to vports.  The
 * tunnel protocol and, for some protocols, tunnel-specific information (e.g.,
 * for VXLAN, the UDP destination port number) are always use as part of the
 * mapping.  Which other fields are used for the mapping depends on the vports
 * themselves (the parenthesized notations refer to "struct tnl_match" fields):
 *
 *     - in_key: A vport may match a specific tunnel ID (in_key_flow == false)
 *       or arrange for the tunnel ID to be matched as tunnel.tun_id in the
 *       OpenFlow flow (in_key_flow == true).
 *
 *     - ip_dst: A vport may match a specific destination IP address
 *       (ip_dst_flow == false) or arrange for the destination IP to be matched
 *       as tunnel.ip_dst in the OpenFlow flow (ip_dst_flow == true).
 *
 *     - ip_src: A vport may match a specific IP source address (ip_src_flow ==
 *       false, ip_src != 0), wildcard all source addresses (ip_src_flow ==
 *       false, ip_src == 0), or arrange for the IP source address to be
 *       handled in the OpenFlow flow table (ip_src_flow == true).
 *
 * Thus, there are 2 * 2 * 3 == 12 possible ways a vport can match against a
 * tunnel packet.  We number the possibilities for each field in increasing
 * order as listed in each bullet above.  We order the 12 overall combinations
 * in lexicographic order considering in_key first, then ip_dst, then
 * ip_src. */
#define N_MATCH_TYPES (3 * 3 * 3 * 2 * 2)

/* The three possibilities (see above) for vport ip_src matches. */
enum match_type {
    MATCH_CFG,             /* ip_src must equal configured address. */
    MATCH_ANY,             /* Any ip_src is acceptable. */
    MATCH_FLOW             /* ip_src is handled in flow table. */
};

/* Each hmap contains "struct tnl_port"s.
 * The index is a combination of how each of the fields listed under "Tunnel
 * matches" above matches, see the final paragraph for ordering. */
static struct hmap *tnl_match_maps[N_MATCH_TYPES] OVS_GUARDED_BY(rwlock);
static struct hmap **tnl_match_map(const struct tnl_match *);

static struct hmap tnl_smac_map = HMAP_INITIALIZER(&tnl_smac_map);
static void tnl_smac_add(
        const struct ofproto_dpif *, const struct netdev_tunnel_config *cfg);
static void tnl_smac_delete(
        const struct ofproto_dpif *, const struct netdev_tunnel_config *cfg);

static struct hmap ofport_map__ = HMAP_INITIALIZER(&ofport_map__);
static struct hmap *ofport_map OVS_GUARDED_BY(rwlock) = &ofport_map__;

static struct vlog_rate_limit rl = VLOG_RATE_LIMIT_INIT(1, 5);
static struct vlog_rate_limit dbg_rl = VLOG_RATE_LIMIT_INIT(60, 60);

static struct tnl_port *tnl_find(const struct flow *) OVS_REQ_RDLOCK(rwlock);
static struct tnl_port *tnl_find_exact(struct tnl_match *, struct hmap *)
    OVS_REQ_RDLOCK(rwlock);
static struct tnl_port *tnl_find_ofport(const struct ofport_dpif *)
    OVS_REQ_RDLOCK(rwlock);

static uint32_t tnl_hash(struct tnl_match *);
static void tnl_match_fmt(const struct tnl_match *, struct ds *);
static char *tnl_port_to_string(const struct tnl_port *)
    OVS_REQ_RDLOCK(rwlock);
static void tnl_port_format(const struct tnl_port *, struct ds *)
    OVS_REQ_RDLOCK(rwlock);
static void tnl_port_mod_log(const struct tnl_port *, const char *action)
    OVS_REQ_RDLOCK(rwlock);
static const char *tnl_port_get_name(const struct tnl_port *)
    OVS_REQ_RDLOCK(rwlock);
static void tnl_port_del__(const struct ofproto_dpif *,
        const struct ofport_dpif *, odp_port_t)
    OVS_REQ_WRLOCK(rwlock);

static unixctl_cb_func tnl_unixctl_list;

void
ofproto_tunnel_init(void)
{
    static struct ovsthread_once once = OVSTHREAD_ONCE_INITIALIZER;

    if (ovsthread_once_start(&once)) {
        fat_rwlock_init(&rwlock);
        unixctl_command_register("ofproto/list-tunnels", "", 0, 0,
                                 tnl_unixctl_list, NULL);
        ovsthread_once_done(&once);
    }
}

static bool
tnl_port_add__(const struct ofproto_dpif *ofproto OVS_UNUSED, const struct ofport_dpif *ofport,
               const struct netdev *netdev, odp_port_t odp_port, bool warn,
               bool native_tnl, const char name[])
    OVS_REQ_WRLOCK(rwlock)
{
    const struct netdev_tunnel_config *cfg;
    struct tnl_port *existing_port;
    struct tnl_port *tnl_port;
    struct hmap **map;

    cfg = netdev_get_tunnel_config(netdev);
    ovs_assert(cfg);

    tnl_port = xzalloc(sizeof *tnl_port);
    tnl_port->ofport = ofport;
    tnl_port->netdev = netdev_ref(netdev);
    tnl_port->change_seq = netdev_get_change_seq(tnl_port->netdev);

    tnl_port->match.in_key = cfg->in_key;
    tnl_port->match.ipv6_src = cfg->ipv6_src;
    tnl_port->match.ipv6_dst = cfg->ipv6_dst;
    tnl_port->match.ip_src_flow = cfg->ip_src_flow;
    tnl_port->match.ip_dst_flow = cfg->ip_dst_flow;
    tnl_port->match.in_key_flow = cfg->in_key_flow;
    tnl_port->match.pt_mode = netdev_get_pt_mode(netdev);

    tnl_port->match.dl_port_flow = cfg->dl_port_flow;
    tnl_port->match.vlan_id_flow = cfg->vlan_id_flow;
    tnl_port->match.odp_port = odp_port;
    if (cfg->dl_port_name) {
        if (ofproto_port_info_query_by_name(cfg->dl_port_name,
                    &tnl_port->match.dl_odp_port, &tnl_port->dl_ofp_port)) {
            netdev_close(tnl_port->netdev);
            free(tnl_port);
            return false;
        }
    }

    tnl_port->match.vlan_id = (OVS_FORCE ovs_be16)cfg->vlan_id;
    tnl_smac_add(ofproto, cfg);
    map = tnl_match_map(&tnl_port->match);
    existing_port = tnl_find_exact(&tnl_port->match, *map);
    if (existing_port) {
        if (warn) {
            struct ds ds = DS_EMPTY_INITIALIZER;
            tnl_match_fmt(&tnl_port->match, &ds);
            VLOG_WARN("%s: attempting to add tunnel port with same config as "
                      "port '%s' (%s)", tnl_port_get_name(tnl_port),
                      tnl_port_get_name(existing_port), ds_cstr(&ds));
            ds_destroy(&ds);
        }
        netdev_close(tnl_port->netdev);
        free(tnl_port);
        return false;
    }


    hmap_insert(ofport_map, &tnl_port->ofport_node, hash_pointer(ofport, 0));

    if (!*map) {
        *map = xmalloc(sizeof **map);
        hmap_init(*map);
    }
    hmap_insert(*map, &tnl_port->match_node, tnl_hash(&tnl_port->match));
    tnl_port_mod_log(tnl_port, "adding");

    if (native_tnl) {
        const char *type;

        type = netdev_get_type(netdev);
        /* If user specified entire L2 and L3 encap parameters then program the
         * tnl_port_map with the information user provided */
        if (tnl_port->match.dl_odp_port || tnl_port->match.dl_port_flow) {
            tnl_port_map_insert_by_ip(odp_port, cfg->src_mac,
                    &tnl_port->match.ipv6_src, cfg->dst_port, name, type);
        } else {
            tnl_port_map_insert(odp_port, cfg->dst_port, name, type);
        }
    }
    return true;
}

/* Adds 'ofport' to the module with datapath port number 'odp_port'. 'ofport's
 * must be added before they can be used by the module. 'ofport' must be a
 * tunnel.
 *
 * Returns 0 if successful, otherwise a positive errno value. */
int
tnl_port_add(const struct ofproto_dpif *ofproto, const struct ofport_dpif *ofport,
             const struct netdev *netdev, odp_port_t odp_port, bool native_tnl,
             const char name[])
    OVS_EXCLUDED(rwlock)
{
    bool ok;

    fat_rwlock_wrlock(&rwlock);
    ok = tnl_port_add__(ofproto, ofport, netdev, odp_port, true, native_tnl, name);
    fat_rwlock_unlock(&rwlock);

    return ok ? 0 : EEXIST;
}

/* Checks if the tunnel represented by 'ofport' reconfiguration due to changes
 * in its netdev_tunnel_config. If it does, returns true. Otherwise, returns
 * false. 'new_odp_port' should be the port number coming from 'ofport' that
 * is passed to tnl_port_add__(). 'old_odp_port' should be the port number
 * that is passed to tnl_port_del__(). */
bool
tnl_port_reconfigure(const struct ofproto_dpif *ofproto, 
                     const struct ofport_dpif *ofport,
                     const struct netdev *netdev, odp_port_t new_odp_port,
                     odp_port_t old_odp_port, bool native_tnl,
                     const char name[])
    OVS_EXCLUDED(rwlock)
{
    struct tnl_port *tnl_port;
    bool changed = false;

    fat_rwlock_wrlock(&rwlock);
    tnl_port = tnl_find_ofport(ofport);
    if (!tnl_port) {
        changed = tnl_port_add__(ofproto, ofport, netdev, new_odp_port, false,
                                 native_tnl, name);
    } else if (tnl_port->netdev != netdev
               || tnl_port->match.odp_port != new_odp_port
               || tnl_port->change_seq != netdev_get_change_seq(tnl_port->netdev)) {
        VLOG_DBG("reconfiguring %s", tnl_port_get_name(tnl_port));
        tnl_port_del__(ofproto, ofport, old_odp_port);
        tnl_port_add__(ofproto, ofport, netdev, new_odp_port, true, native_tnl, name);
        changed = true;
    }
    fat_rwlock_unlock(&rwlock);
    return changed;
}

static void
tnl_port_del__(const struct ofproto_dpif *ofproto,
               const struct ofport_dpif *ofport, odp_port_t odp_port)
    OVS_REQ_WRLOCK(rwlock)
{
    struct tnl_port *tnl_port;

    if (!ofport) {
        return;
    }

    tnl_port = tnl_find_ofport(ofport);
    if (tnl_port) {
        const struct netdev_tunnel_config *cfg;
        struct hmap **map;
        const char *type;

        cfg = netdev_get_tunnel_config(tnl_port->netdev);

        type = netdev_get_type(tnl_port->netdev);

        if (tnl_port->match.dl_odp_port) {
            tnl_port_map_delete_by_ip(odp_port, cfg->src_mac,
                    &tnl_port->match.ipv6_src, cfg->dst_port, type);
        } else {
            tnl_port_map_delete(odp_port, type);
        }
        tnl_port_mod_log(tnl_port, "removing");
        map = tnl_match_map(&tnl_port->match);
        hmap_remove(*map, &tnl_port->match_node);
        if (hmap_is_empty(*map)) {
            hmap_destroy(*map);
            free(*map);
            *map = NULL;
        }
        hmap_remove(ofport_map, &tnl_port->ofport_node);
        netdev_close(tnl_port->netdev);
        free(tnl_port);

        tnl_smac_delete(ofproto, cfg);
    }
}

/* Removes 'ofport' from the module. */
void
tnl_port_del(const struct ofproto_dpif *ofproto,
             const struct ofport_dpif *ofport, odp_port_t odp_port)
    OVS_EXCLUDED(rwlock)
{
    fat_rwlock_wrlock(&rwlock);
    tnl_port_del__(ofproto, ofport, odp_port);
    fat_rwlock_unlock(&rwlock);
}

/* Looks in the table of tunnels for a tunnel matching the metadata in 'flow'.
 * Returns the 'ofport' corresponding to the new in_port, or a null pointer if
 * none is found.
 *
 * Callers should verify that 'flow' needs to be received by calling
 * tnl_port_should_receive() before this function. */

const struct ofport_dpif *
tnl_port_receive(const struct flow *flow) OVS_EXCLUDED(rwlock)
{
    const struct ofport_dpif *ofport;
    struct tnl_port *tnl_port;

    {
#if 1
        char *s = flow_to_string(flow, NULL);
        PRINTF("dl_port %d, flow: %s", flow->tunnel.dl_port, s);
        free(s);
#endif
    }
    fat_rwlock_rdlock(&rwlock);
    tnl_port = tnl_find(flow);
    ofport = tnl_port ? tnl_port->ofport : NULL;
    if (!tnl_port) {
        if (!VLOG_DROP_WARN(&rl)) {
            char *flow_str = flow_to_string(flow, NULL);
            VLOG_WARN("receive tunnel port not found (%s)", flow_str);
            free(flow_str);
        }
        goto out;
    }

    if (!VLOG_DROP_DBG(&dbg_rl)) {
        char *flow_str = flow_to_string(flow, NULL);
        char *tnl_str = tnl_port_to_string(tnl_port);
        VLOG_DBG("tunnel port %s receive from flow %s", tnl_str, flow_str);
        free(tnl_str);
        free(flow_str);
    }

out:
    fat_rwlock_unlock(&rwlock);
    return ofport;
}

/* Should be called at the beginning of action translation to initialize
 * wildcards and perform any actions based on receiving on tunnel port.
 *
 * Returns false if the packet must be dropped. */
bool
tnl_process_ecn(struct flow *flow)
{
    if (!tnl_port_should_receive(flow)) {
        return true;
    }

    if (is_ip_any(flow) && IP_ECN_is_ce(flow->tunnel.ip_tos)) {
        if ((flow->nw_tos & IP_ECN_MASK) == IP_ECN_NOT_ECT) {
            VLOG_WARN_RL(&rl, "dropping tunnel packet marked ECN CE"
                         " but is not ECN capable");
            return false;
        }

        /* Set the ECN CE value in the tunneled packet. */
        flow->nw_tos |= IP_ECN_CE;
    }

    return true;
}

void
tnl_wc_init(struct flow *flow, struct flow_wildcards *wc)
{
    if (tnl_port_should_receive(flow)) {
        wc->masks.tunnel.tun_id = OVS_BE64_MAX;
        if (flow->tunnel.ip_dst) {
            wc->masks.tunnel.ip_src = OVS_BE32_MAX;
            wc->masks.tunnel.ip_dst = OVS_BE32_MAX;
        } else {
            wc->masks.tunnel.ipv6_src = in6addr_exact;
            wc->masks.tunnel.ipv6_dst = in6addr_exact;
        }
        wc->masks.tunnel.flags = (FLOW_TNL_F_DONT_FRAGMENT |
                                  FLOW_TNL_F_CSUM |
                                  FLOW_TNL_F_KEY);
        wc->masks.tunnel.ip_tos = UINT8_MAX;
        wc->masks.tunnel.ip_ttl = 0;
        /* The tp_src and tp_dst members in flow_tnl are set to be always
         * wildcarded, not to unwildcard them here. */
        wc->masks.tunnel.tp_src = 0;
        wc->masks.tunnel.tp_dst = 0;

        if (is_ip_any(flow)
            && IP_ECN_is_ce(flow->tunnel.ip_tos)) {
            wc->masks.nw_tos |= IP_ECN_MASK;
        }
    }
}

/* Given that 'flow' should be output to the ofport corresponding to
 * 'tnl_port', updates 'flow''s tunnel headers and returns the actual datapath
 * port that the output should happen on.  May return ODPP_NONE if the output
 * shouldn't occur. */
odp_port_t
tnl_port_send(const struct ofport_dpif *ofport, struct flow *flow,
              struct flow_wildcards *wc) OVS_EXCLUDED(rwlock)
{
    const struct netdev_tunnel_config *cfg;
    struct tnl_port *tnl_port;
    char *pre_flow_str = NULL;
    odp_port_t out_port;

    fat_rwlock_rdlock(&rwlock);
    tnl_port = tnl_find_ofport(ofport);
    out_port = tnl_port ? tnl_port->match.odp_port : ODPP_NONE;
    if (!tnl_port) {
        goto out;
    }

    cfg = netdev_get_tunnel_config(tnl_port->netdev);
    ovs_assert(cfg);

    if (!VLOG_DROP_DBG(&dbg_rl)) {
        pre_flow_str = flow_to_string(flow, NULL);
    }

    if (!cfg->ip_src_flow) {
        flow->tunnel.ip_src = in6_addr_get_mapped_ipv4(&tnl_port->match.ipv6_src);
        if (!flow->tunnel.ip_src) {
            flow->tunnel.ipv6_src = tnl_port->match.ipv6_src;
        } else {
            flow->tunnel.ipv6_src = in6addr_any;
        }
    }
    if (!cfg->ip_dst_flow) {
        flow->tunnel.ip_dst = in6_addr_get_mapped_ipv4(&tnl_port->match.ipv6_dst);
        if (!flow->tunnel.ip_dst) {
            flow->tunnel.ipv6_dst = tnl_port->match.ipv6_dst;
        } else {
            flow->tunnel.ipv6_dst = in6addr_any;
        }
    }
    flow->tunnel.tp_dst = cfg->dst_port;
    if (!cfg->out_key_flow) {
        flow->tunnel.tun_id = cfg->out_key;
    }

    if (cfg->ttl_inherit && is_ip_any(flow)) {
        wc->masks.nw_ttl = 0xff;
        flow->tunnel.ip_ttl = flow->nw_ttl;
    } else {
        flow->tunnel.ip_ttl = cfg->ttl;
    }

    if (cfg->tos_inherit && is_ip_any(flow)) {
        wc->masks.nw_tos |= IP_DSCP_MASK;
        flow->tunnel.ip_tos = flow->nw_tos & IP_DSCP_MASK;
    } else {
        flow->tunnel.ip_tos = cfg->tos;
    }

    /* ECN fields are always inherited. */
    if (is_ip_any(flow)) {
        wc->masks.nw_tos |= IP_ECN_MASK;

        if (IP_ECN_is_ce(flow->nw_tos)) {
            flow->tunnel.ip_tos |= IP_ECN_ECT_0;
        } else {
            flow->tunnel.ip_tos |= flow->nw_tos & IP_ECN_MASK;
        }
    }

    flow->tunnel.flags &= ~(FLOW_TNL_F_MASK & ~FLOW_TNL_PUB_F_MASK);
    flow->tunnel.flags |= (cfg->dont_fragment ? FLOW_TNL_F_DONT_FRAGMENT : 0)
        | (cfg->csum ? FLOW_TNL_F_CSUM : 0)
        | (cfg->out_key_present ? FLOW_TNL_F_KEY : 0);

    if (cfg->set_egress_pkt_mark) {
        flow->pkt_mark = cfg->egress_pkt_mark;
        wc->masks.pkt_mark = UINT32_MAX;
    }

    if (!cfg->erspan_ver_flow) {
        flow->tunnel.erspan_ver = cfg->erspan_ver;
    }

    if (!cfg->erspan_idx_flow) {
        flow->tunnel.erspan_idx = cfg->erspan_idx;
    }

    if (!cfg->erspan_dir_flow) {
        flow->tunnel.erspan_dir = cfg->erspan_dir;
    }

    if (!cfg->erspan_hwid_flow) {
        flow->tunnel.erspan_hwid = cfg->erspan_hwid;
    }

    if (!cfg->dl_port_flow) {
        flow->tunnel.dl_port = tnl_port->dl_ofp_port;
        wc->masks.tunnel.dl_port = OVS_BE32_MAX;

        wc->masks.tunnel.eth_src = eth_addr_exact;
        flow->tunnel.eth_src = cfg->src_mac;

        if (!cfg->dst_mac_flow) {
            wc->masks.tunnel.eth_dst = eth_addr_exact;
            flow->tunnel.eth_dst = cfg->dst_mac;
        }
        if (!cfg->vlan_id_flow) {
            flow->tunnel.vlan_id = (OVS_FORCE ovs_be16)cfg->vlan_id;
            wc->masks.tunnel.vlan_id = OVS_BE16_MAX;
        }
    }

    if (pre_flow_str) {
        char *post_flow_str = flow_to_string(flow, NULL);
        char *tnl_str = tnl_port_to_string(tnl_port);
        VLOG_DBG("flow sent\n"
                 "%s"
                 " pre: %s\n"
                 "post: %s",
                 tnl_str, pre_flow_str, post_flow_str);
        free(tnl_str);
        free(pre_flow_str);
        free(post_flow_str);
    }

out:
    fat_rwlock_unlock(&rwlock);
    return out_port;
}

static uint32_t
tnl_hash(struct tnl_match *match)
{
    BUILD_ASSERT_DECL(sizeof *match % sizeof(uint32_t) == 0);
    return hash_words((uint32_t *) match, sizeof *match / sizeof(uint32_t), 0);
}

static struct tnl_port *
tnl_find_ofport(const struct ofport_dpif *ofport) OVS_REQ_RDLOCK(rwlock)
{
    struct tnl_port *tnl_port;

    HMAP_FOR_EACH_IN_BUCKET (tnl_port, ofport_node, hash_pointer(ofport, 0),
                             ofport_map) {
        if (tnl_port->ofport == ofport) {
            return tnl_port;
        }
    }
    return NULL;
}

static struct tnl_port *
tnl_find_exact(struct tnl_match *match, struct hmap *map)
    OVS_REQ_RDLOCK(rwlock)
{
    if (map) {
        struct tnl_port *tnl_port;

        {
            struct ds ds = DS_EMPTY_INITIALIZER;
            tnl_match_fmt(match, &ds);
            PRINTF("matching (%s)", ds_cstr(&ds));
            ds_destroy(&ds);
        }

        HMAP_FOR_EACH_WITH_HASH (tnl_port, match_node, tnl_hash(match), map) {
            if (!memcmp(match, &tnl_port->match, sizeof *match)) {
                return tnl_port;
            }
        }
    }
    return NULL;
}

/* Returns the tnl_port that is the best match for the tunnel data in 'flow',
 * or NULL if no tnl_port matches 'flow'. */
static struct tnl_port *
tnl_find(const struct flow *flow) OVS_REQ_RDLOCK(rwlock)
{
    enum match_type ip_src, dl_odp_port, vlan_id;
    int in_key_flow;
    int ip_dst_flow;
    int i;

    i = 0;
    for (dl_odp_port = 0; dl_odp_port < 3; dl_odp_port++) {
        for (vlan_id = 0; vlan_id < 3; vlan_id++) {
            for (in_key_flow = 0; in_key_flow < 2; in_key_flow++) {
                for (ip_dst_flow = 0; ip_dst_flow < 2; ip_dst_flow++) {
                    for (ip_src = 0; ip_src < 3; ip_src++) {
                        struct hmap *map = tnl_match_maps[i];

                        if (map) {
                            struct tnl_port *tnl_port;
                            struct tnl_match match;

                            PRINTF("Bucket: {%d,%d,%d,%d,%d}",
                                    dl_odp_port, vlan_id, in_key_flow, ip_dst_flow, ip_src);

                            memset(&match, 0, sizeof match);

                            /* The apparent mix-up of 'ip_dst' and 'ip_src' below is
                             * correct, because "struct tnl_match" is expressed in
                             * terms of packets being sent out, but we are using it
                             * here as a description of how to treat received
                             * packets. */
                            match.in_key = in_key_flow ? 0 : flow->tunnel.tun_id;
                            if (ip_src == MATCH_CFG) {
                                match.ipv6_src = flow_tnl_dst(&flow->tunnel);
                            }
                            if (!ip_dst_flow) {
                                match.ipv6_dst = flow_tnl_src(&flow->tunnel);
                            }
                            match.odp_port = flow->in_port.odp_port;
                            match.in_key_flow = in_key_flow;
                            match.ip_dst_flow = ip_dst_flow;
                            match.ip_src_flow = ip_src == MATCH_FLOW;

                            match.vlan_id_flow = vlan_id == MATCH_FLOW;
                            match.vlan_id = (vlan_id == MATCH_CFG) ? flow->tunnel.vlan_id : 0;

                            match.dl_port_flow = dl_odp_port == MATCH_FLOW;
                            match.dl_odp_port = (dl_odp_port == MATCH_CFG) ? flow->tunnel.dl_port : 0;

                            /* Look for a legacy L2 or L3 tunnel port first. */
                            if (pt_ns(flow->packet_type) == OFPHTN_ETHERTYPE) {
                                match.pt_mode = NETDEV_PT_LEGACY_L3;
                            } else {
                                match.pt_mode = NETDEV_PT_LEGACY_L2;
                            }
                            tnl_port = tnl_find_exact(&match, map);
                            if (tnl_port) {
                                return tnl_port;
                            }

                            /* Then check for a packet type aware port. */
                            match.pt_mode = NETDEV_PT_AWARE;
                            tnl_port = tnl_find_exact(&match, map);
                            if (tnl_port) {
                                return tnl_port;
                            }
                        }

                        i++;
                    }
                }
            }
        }
    }

    return NULL;
}

/* Returns a pointer to the 'tnl_match_maps' element corresponding to 'm''s
 * matching criteria. */
static struct hmap **
tnl_match_map(const struct tnl_match *m)
{
    enum match_type ip_src, dl_odp_port, vlan_id;

    ip_src = (m->ip_src_flow ? MATCH_FLOW
              : ipv6_addr_is_set(&m->ipv6_src) ? MATCH_CFG
              : MATCH_ANY);

    dl_odp_port = (m->dl_port_flow ? MATCH_FLOW
              : m->dl_odp_port ? MATCH_CFG
              : MATCH_ANY);

    vlan_id = (m->vlan_id_flow ? MATCH_FLOW
              : m->vlan_id ? MATCH_CFG
              : MATCH_ANY);

    PRINTF("tnl_match_map: {%d,%d,%d,%d,%d}", dl_odp_port, vlan_id,
            m->in_key_flow, m->ip_dst_flow, ip_src);

    return &tnl_match_maps[
        36 * dl_odp_port +
        12 * vlan_id + 
        6 * m->in_key_flow + 3 * m->ip_dst_flow + ip_src];
}

static void
tnl_smac_add(const struct ofproto_dpif *ofproto,
             const struct netdev_tunnel_config *cfg)
{
    struct tnl_smac_entry entry, *pEntry;

    if (!cfg->dl_port_name || cfg->vlan_id_flow) {
        return;
    }

    entry.mac = cfg->src_mac;
    entry.vlan = cfg->vlan_id;

    HMAP_FOR_EACH_WITH_HASH (pEntry, node, hash_words((uint32_t *) &entry, 2, 0), &tnl_smac_map) {
        pEntry->ref_cnt++;
        return;
    }
    
    pEntry = xzalloc(sizeof *pEntry);
    memcpy(pEntry, &entry, sizeof *pEntry);
    pEntry->ref_cnt = 1;

    hmap_insert(&tnl_smac_map, &pEntry->node, hash_words((uint32_t *) pEntry, 2, 0));

    xlate_add_static_mac_entry(ofproto, OFPP_LOCAL, cfg->src_mac, cfg->vlan_id);
    return;
}

static void
tnl_smac_delete(const struct ofproto_dpif *ofproto,
                const struct netdev_tunnel_config *cfg)
{
    struct tnl_smac_entry entry, *pEntry = NULL;

    /* If tunnel has l2 specification proceed */
    if (!cfg->dl_port_name || cfg->vlan_id_flow) {
        return;
    }

    entry.mac = cfg->src_mac;
    entry.vlan = cfg->vlan_id;

    /* Lookup src_mac in tnl_smac_map */
    HMAP_FOR_EACH_WITH_HASH (pEntry, node, hash_words((uint32_t *) &entry, 2, 0), &tnl_smac_map) {
        /* Decrement reference count */
        if (--pEntry->ref_cnt) {
            return;
        }
        xlate_delete_static_mac_entry(ofproto, cfg->src_mac, cfg->vlan_id);
        hmap_remove(&tnl_smac_map, &pEntry->node);

        free(pEntry);
        break;
    }

}

static void
tnl_match_fmt(const struct tnl_match *match, struct ds *ds)
    OVS_REQ_RDLOCK(rwlock)
{
    if (!match->ip_dst_flow) {
        ipv6_format_mapped(&match->ipv6_src, ds);
        ds_put_cstr(ds, "->");
        ipv6_format_mapped(&match->ipv6_dst, ds);
    } else if (!match->ip_src_flow) {
        ipv6_format_mapped(&match->ipv6_src, ds);
        ds_put_cstr(ds, "->flow");
    } else {
        ds_put_cstr(ds, "flow->flow");
    }

    if (match->in_key_flow) {
        ds_put_cstr(ds, ", key=flow");
    } else {
        ds_put_format(ds, ", key=%#"PRIx64, ntohll(match->in_key));
    }

    const char *pt_mode
        = (match->pt_mode == NETDEV_PT_LEGACY_L2 ? "legacy_l2"
           : match->pt_mode == NETDEV_PT_LEGACY_L3 ? "legacy_l3"
           : "ptap");
    ds_put_format(ds, ", %s, dp port=%"PRIu32, pt_mode, match->odp_port);

    if (match->vlan_id_flow) {
        ds_put_format(ds, ", vlan_id=flow");
    } else if (match->vlan_id) {
        ds_put_format(ds, ", vlan_id=%#"PRIx16, match->vlan_id);
    }
    if (match->dl_port_flow) {
        ds_put_format(ds, ", out_port=flow");
    } else if (match->dl_odp_port) {
        ds_put_format(ds, ", out_port=%"PRIu32, match->dl_odp_port);
    }
}

static void
tnl_port_mod_log(const struct tnl_port *tnl_port, const char *action)
    OVS_REQ_RDLOCK(rwlock)
{
    if (VLOG_IS_DBG_ENABLED()) {
        struct ds ds = DS_EMPTY_INITIALIZER;

        tnl_match_fmt(&tnl_port->match, &ds);
        VLOG_INFO("%s tunnel port %s (%s)", action,
                  tnl_port_get_name(tnl_port), ds_cstr(&ds));
        ds_destroy(&ds);
    }
}

static void OVS_REQ_RDLOCK(rwlock)
tnl_port_format(const struct tnl_port *tnl_port, struct ds *ds)
{
    const struct netdev_tunnel_config *cfg =
        netdev_get_tunnel_config(tnl_port->netdev);

    ds_put_format(ds, "port %"PRIu32": %s (%s: ", tnl_port->match.odp_port,
                  tnl_port_get_name(tnl_port),
                  netdev_get_type(tnl_port->netdev));
    tnl_match_fmt(&tnl_port->match, ds);

    if (cfg->out_key != cfg->in_key ||
        cfg->out_key_present != cfg->in_key_present ||
        cfg->out_key_flow != cfg->in_key_flow) {
        ds_put_cstr(ds, ", out_key=");
        if (!cfg->out_key_present) {
            ds_put_cstr(ds, "none");
        } else if (cfg->out_key_flow) {
            ds_put_cstr(ds, "flow");
        } else {
            ds_put_format(ds, "%#"PRIx64, ntohll(cfg->out_key));
        }
    }

    if (cfg->ttl_inherit) {
        ds_put_cstr(ds, ", ttl=inherit");
    } else {
        ds_put_format(ds, ", ttl=%"PRIu8, cfg->ttl);
    }

    if (cfg->tos_inherit) {
        ds_put_cstr(ds, ", tos=inherit");
    } else if (cfg->tos) {
        ds_put_format(ds, ", tos=%#"PRIx8, cfg->tos);
    }

    if (!cfg->dont_fragment) {
        ds_put_cstr(ds, ", df=false");
    }

    if (cfg->csum) {
        ds_put_cstr(ds, ", csum=true");
    }

    ds_put_cstr(ds, ")\n");
}

static char * OVS_REQ_RDLOCK(rwlock)
tnl_port_to_string(const struct tnl_port *tnl_port)
{
    struct ds ds = DS_EMPTY_INITIALIZER;
    tnl_port_format(tnl_port, &ds);
    return ds_steal_cstr(&ds);
}

static const char *
tnl_port_get_name(const struct tnl_port *tnl_port) OVS_REQ_RDLOCK(rwlock)
{
    return netdev_get_name(tnl_port->netdev);
}

const char *
tnl_port_get_type(const struct ofport_dpif *ofport) OVS_REQ_RDLOCK(rwlock)
{
    struct tnl_port *tnl_port;

    tnl_port = tnl_find_ofport(ofport);
    return !tnl_port ? NULL :
                       netdev_get_type(tnl_port->netdev);
}

int
tnl_port_build_header(const struct ofport_dpif *ofport,
                      struct ovs_action_push_tnl *data,
                      const struct netdev_tnl_build_header_params *params)
{
    struct tnl_port *tnl_port;
    int res;

    fat_rwlock_rdlock(&rwlock);
    tnl_port = tnl_find_ofport(ofport);
    ovs_assert(tnl_port);
    res = netdev_build_header(tnl_port->netdev, data, params);
    fat_rwlock_unlock(&rwlock);

    return res;
}

static void
tnl_unixctl_list(struct unixctl_conn *conn,
                 int argc OVS_UNUSED, const char *argv[] OVS_UNUSED,
                 void *aux OVS_UNUSED)
{
    struct ds reply = DS_EMPTY_INITIALIZER;

    fat_rwlock_rdlock(&rwlock);
    for (int i = 0; i < N_MATCH_TYPES; i++) {
        struct hmap *map = tnl_match_maps[i];
        if (map) {
            struct tnl_port *tnl_port;
            HMAP_FOR_EACH (tnl_port, match_node, map) {
                // ds_put_format(&reply, "bucket %d, ", i);
                tnl_port_format(tnl_port, &reply);
            }
        }
    }
    fat_rwlock_unlock(&rwlock);

    unixctl_command_reply(conn, ds_cstr(&reply));
    ds_destroy(&reply);
}
