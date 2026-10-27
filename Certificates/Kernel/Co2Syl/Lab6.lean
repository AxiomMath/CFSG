module

public import Certificates.Kernel.Co2Syl.D6
import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSpor.Co2Syl

open CFSG.KC.Co2Syl

theorem lab6 : ∀ t < 16384, labK E6.CF G6 LD6 (RP 6) 16384 t = true := by
  kc_cover 64

end CertificateChecks.KernelSpor.Co2Syl

end
