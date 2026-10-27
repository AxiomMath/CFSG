module

public import Certificates.Kernel.Co2Cls.D4
import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSpor.Co2Cls

open CFSG.KC.Co2Cls CertificateChecks.KernelSpor.Co2Syl

theorem rec4a : ∀ t < 16384, recC C4 GC 21 (RP 4) 22680 (Nat.add 0 t) = true := by kc_cover 64

end CertificateChecks.KernelSpor.Co2Cls

end
