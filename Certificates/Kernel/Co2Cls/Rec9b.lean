module

public import Certificates.Kernel.Co2Cls.D9
import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSpor.Co2Cls

open CFSG.KC.Co2Cls CertificateChecks.KernelSpor.Co2Syl

theorem rec9b : ∀ t < 16384, recC C9 GC 21 (RP 9) 120960 (Nat.add 16384 t) = true := by
  kc_cover 64

end CertificateChecks.KernelSpor.Co2Cls

end
