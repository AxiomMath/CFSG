module

public import Certificates.Kernel.Co2SmithS.PinData
public import Certificates.Data.Kernel.Co2SmithS.Pin
import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo2SmithS

open CFSG.KC.Co2SmithS

theorem pin_ok : ∀ c < 65536, (!pinK SR c || c == 24505) = true := by kc_cover 1024

end CertificateChecks.KernelCo2SmithS

end
