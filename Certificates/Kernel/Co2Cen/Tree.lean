module

public import Certificates.Kernel.Co2Cen.Data
public import Certificates.Kernel.Co2JRank.Data
public import Certificates.Kernel.Co2Syl.Small
import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSpor.Co2Cen

open CFSG.KC.Co2Cen CertificateChecks.KernelSpor.Co2Syl

theorem tree : ∀ s < 64, recW TW G1 Co2JRank.WG 5 64 s = true := by kc_cover 64

end CertificateChecks.KernelSpor.Co2Cen

end
