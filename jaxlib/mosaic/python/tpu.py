# Copyright 2023 The JAX Authors.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     https://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""Python bindings for the MLIR TPU dialect."""

# flake8: noqa: F401
# flake8: noqa: F403

# pylint: disable=g-bad-import-order
from ._tpu_gen import *  # pylint: disable=wildcard-import
from ._tpu_ext import *  # pylint: disable=wildcard-import
