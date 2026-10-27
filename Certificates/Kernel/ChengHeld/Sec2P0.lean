module

public import Certificates.Kernel.ChengHeld.Sec2
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelChengHeld.S2

open CFSG.KC.ChengHeldS2

theorem k0_pf : pairFixK 256 m0 i0 (aR (AU0 0)) (aR (AU0 1)) = true := by decide +kernel

end CertificateChecks.KernelChengHeld.S2

end
