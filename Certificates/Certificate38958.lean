module

public import Certificates.Data.GF2W1112Co2U
import Certificates.Kernel.Co2U.Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate38958 : CFSG.GF2W1112.w12UCheck2 () = true :=
  KernelCo2U.check2

end Certificates
