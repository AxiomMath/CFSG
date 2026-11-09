module

public import Certificates.Kernel.Co2Jc.OffTw
import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo2Jc

theorem step0_q : ∀ t < 24, stepR (32 * (0 + t / 4) + t % 4 * 8) 8 = true := by
  kc_cover 1

theorem step0_k : ∀ d < 6, stepC (0 + d) = true := stepC_of_pieces 0 6 step0_q

end CertificateChecks.KernelCo2Jc
