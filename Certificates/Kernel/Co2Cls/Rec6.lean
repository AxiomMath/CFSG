module

public import Certificates.Kernel.Co2Cls.D6
import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSpor.Co2Cls

open CFSG.KC.Co2Cls CertificateChecks.KernelSpor.Co2Syl

theorem rec6 : ∀ k < 15120, recC C6 GC 21 (RP 6) 15120 k = true := by kc_cover 64

end CertificateChecks.KernelSpor.Co2Cls

end
