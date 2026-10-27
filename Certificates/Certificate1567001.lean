module

public import Certificates.Data.McLFivePairs
import Certificates.Kernel.McL5Pairs.Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate1567001 : Certificates.McLFivePairs.check () = true :=
  KernelMcL5Pairs.check_true

end Certificates
