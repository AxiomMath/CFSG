module

public import Certificates.Data.Kernel.AE117Adj

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelCensus

theorem adjCheckL_seven : Certificates.Kernel.AE117Adj.adjCheckL 7 = true := by decide +kernel

end CertificateChecks.KernelCensus
