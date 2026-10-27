module

public import Certificates.Kernel.Cert690.PglGlue

public section

namespace Certificates

open CertificateChecks

open CFSG in
theorem certificate690001 : CFSG.GF2Type.Smith1979W3.Cert690.pglFactsCheck () = true :=
  KernelC690.Pgl.pglFactsP

end Certificates
