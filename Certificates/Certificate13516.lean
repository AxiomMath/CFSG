module

public import CFSG.HardMathSupport.Solomon.Coordinator.I24_7FiCoverData
import Certificates.Kernel.Fi22Cover.Facts
public import CFSG.Monster.B.Fischer.PinnedChainBase

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.Monster.B.Fischer in
theorem certificate13516 : Fi22CoverData ↥fi22P :=
  KernelFi22Cover.fi22CoverData_kernel

end Certificates
