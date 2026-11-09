module

public import Certificates.Data.GF2W1112Co2U
import Certificates.Kernel.Co2U.Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate38959 : CFSG.GF2W1112.w12UCheck3 () = true :=
  KernelCo2U.check3

end Certificates
