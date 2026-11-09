module

public import Certificates.Kernel.Co2Jc.OffTw
import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo2Jc

theorem step2_q : ∀ t < 24, stepR (32 * (12 + t / 4) + t % 4 * 8) 8 = true := by
  kc_cover 1

theorem step2_k : ∀ d < 6, stepC (12 + d) = true := stepC_of_pieces 12 6 step2_q

end CertificateChecks.KernelCo2Jc
