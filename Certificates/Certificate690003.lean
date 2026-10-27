module

public import Certificates.Kernel.Cert690.SqA8Glue5

public section

namespace Certificates

open CertificateChecks

open CFSG in
theorem certificate690003 : CFSG.GF2Type.Smith1979W3.Cert690.a8SquareCheck () = true :=
  KernelC690.SqPass.a8SquareP

end Certificates
