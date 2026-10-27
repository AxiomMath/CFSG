module

public import Certificates.Kernel.ChengHeld.Sec2
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelChengHeld.S2

open CFSG.KC.ChengHeldS2

theorem k1_pf : pairFixK 256 m1 i1 (aR (AU1 0)) (aR (AU1 1)) = true := by decide +kernel

end CertificateChecks.KernelChengHeld.S2

end
