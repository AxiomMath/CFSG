module

public import CFSG.GF2Type.Smith1979.W4C2Check
import Certificates.Kernel.W4C2.Final

public section

namespace Certificates

open CertificateChecks

theorem certificate330390 : CFSG.GF2Type.Smith1979.W4C2.chk = true :=
  KernelW4C2.chk_true

end Certificates
