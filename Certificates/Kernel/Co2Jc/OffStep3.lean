module

public import Certificates.Kernel.Co2Jc.OffTw
import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo2Jc

theorem step3_k : ∀ d < 5, stepC (18 + d) = true := by kc_cover 1

end CertificateChecks.KernelCo2Jc
