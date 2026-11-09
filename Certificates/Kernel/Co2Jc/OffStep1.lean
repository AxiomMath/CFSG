module

public import Certificates.Kernel.Co2Jc.OffTw
import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo2Jc

theorem step1_q : ∀ t < 24, stepR (32 * (6 + t / 4) + t % 4 * 8) 8 = true := by
  kc_cover 1

theorem step1_k : ∀ d < 6, stepC (6 + d) = true := stepC_of_pieces 6 6 step1_q

end CertificateChecks.KernelCo2Jc
