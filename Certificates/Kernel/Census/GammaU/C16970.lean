module

public import Certificates.Data.Kernel.GammaUList

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelCensus

theorem resConjCheckL_eq : Certificates.Kernel.GammaUList.resConjCheckL = true := by
  decide +kernel

end CertificateChecks.KernelCensus
