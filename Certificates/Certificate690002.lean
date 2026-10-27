module

public import Certificates.Kernel.Cert690.SqPglGlue4

public section

namespace Certificates

open CertificateChecks

open CFSG in
theorem certificate690002 : CFSG.GF2Type.Smith1979W3.Cert690.pglSquareCheck () = true :=
  KernelC690.SqPgl.pglSquareP

end Certificates
