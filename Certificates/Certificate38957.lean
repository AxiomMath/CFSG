module

public import Certificates.Data.GF2W1112Co2U
import Certificates.Kernel.Co2U.Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate38957 : CFSG.GF2W1112.w12UCheck1 () = true :=
  KernelCo2U.check1

end Certificates
