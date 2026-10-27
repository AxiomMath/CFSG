module

public import CFSG.Quasithin.Background.F7TwoInvSporJ2Inputs
import Certificates.Kernel.J2Cover.F7Inv7415

public section

namespace Certificates

open CertificateChecks

theorem certificate7415 : CFSG.Quasithin.F7Two.j2InvChk () = true :=
  KernelJ2Cover.j2InvChk_K

end Certificates
