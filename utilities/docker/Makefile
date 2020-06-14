export OVS_BRANCH=cello
export OVS_VERSION=cello
# export KERNEL_VERSION=5.3.0-51-generic
export KERNEL_VERSION=host
export DISTRO=debian
export GITHUB_SRC=https://github.com/vasu-dasari/ovs.git
export DOCKER_REPO=vdasari/ovs

# Example:
#   make build
#   make push

REPO = ${DOCKER_REPO}
tag = ${OVS_VERSION}_${DISTRO}_${KERNEL_VERSION}

build: ;docker build -t ${REPO}:${tag} --build-arg DISTRO=${DISTRO} \
--build-arg OVS_BRANCH=${OVS_BRANCH} \
--build-arg KERNEL_VERSION=${KERNEL_VERSION} \
--build-arg GITHUB_SRC=${GITHUB_SRC} -f ${DISTRO}/Dockerfile .

.PHONY: build

push: ;docker push ${REPO}:${tag}
