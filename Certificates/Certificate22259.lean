module

public import Certificates.Data.SolMaxThreeCent
import Certificates.Kernel.SolMax.ThreeCentF

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.SolMax.ThreeCent in
theorem certificate22259 : threeCentCheck = true :=
  KernelSolMax.ThreeCent.threeCent_true

end Certificates
