module

public import CFSG.LocalAnalysis.StandardType.GGLieCoreA3LatticeE6Defs
import Certificates.Kernel.A3E6.Wire

public section

namespace Certificates

open CertificateChecks

theorem certificate715503 : CFSG.StandardType.LieCore.A3SpecE6Struct :=
  KernelA3E6.a3SpecE6Struct_kernel

end Certificates
