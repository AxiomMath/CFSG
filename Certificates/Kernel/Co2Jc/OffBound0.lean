module

public import Certificates.Kernel.Co2Jc.OffTw
import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo2Jc

theorem bound0_k : ∀ d < 12, boundC (0 + d) = true := by kc_cover 1

end CertificateChecks.KernelCo2Jc
