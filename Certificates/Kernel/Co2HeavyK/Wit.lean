module

public import Certificates.Kernel.Co2HeavyK.Data
import CFSG.Certificates.Kernel.Common.Cover
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo2HeavyK

open CFSG.KC.Co2HeavyK CertificateChecks.KernelSpor.Co2Inv

theorem wit_all : ∀ t < 6144, witK E.CF SQ W RP t = true := by
  kc_cover 64

theorem l2_count : l2K W = true := by quickRfl

theorem norm_all : ∀ t < 6144, normK SQ W (MT 0) (MT 1) t = true := by
  kc_cover 64

end CertificateChecks.KernelCo2HeavyK

end
