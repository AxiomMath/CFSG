module

public import Certificates.Kernel.Co2Syl.D8
import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSpor.Co2Syl

open CFSG.KC.Co2Syl

theorem lab8 : ∀ t < 16384, labK E8.CF G8 LD8 (RP 8) 16384 t = true := by
  kc_cover 64

end CertificateChecks.KernelSpor.Co2Syl

end
