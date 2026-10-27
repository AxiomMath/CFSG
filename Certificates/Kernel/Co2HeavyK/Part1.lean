module

public import Certificates.Kernel.Co2HeavyK.Data
import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo2HeavyK

open CFSG.KC.Co2HeavyK CertificateChecks.KernelSpor.Co2Inv

theorem part1_all : ∀ t < 31, part1K E.CF SQ RP t = true := by
  kc_cover 1

end CertificateChecks.KernelCo2HeavyK

end
