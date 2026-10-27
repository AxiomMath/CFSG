module

public import Certificates.Kernel.Co2HeavyK.Data
import CFSG.Certificates.Kernel.Common.Cover
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo2HeavyK

open CFSG.KC.Co2HeavyK CertificateChecks.KernelSpor.Co2Inv

theorem bind_all : ∀ t < 6144, bindK E.CF SQ W CA t = true := by
  kc_cover 64

theorem ca_ends : caK CA = true := by quickRfl

end CertificateChecks.KernelCo2HeavyK

end
