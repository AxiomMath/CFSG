module

public import Certificates.Kernel.Co2Cls.DS
import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSpor.Co2Cls

open CFSG.KC.Co2Cls CertificateChecks.KernelSpor.Co2Syl

theorem rec0 : ∀ k < 1, recC C0 GC 21 (RP 0) 1 k = true := by kc_cover 64
theorem rec1 : ∀ k < 270, recC C1 GC 21 (RP 1) 270 k = true := by kc_cover 64
theorem rec2 : ∀ k < 1260, recC C2 GC 21 (RP 2) 1260 k = true := by kc_cover 64
theorem rec3 : ∀ k < 1260, recC C3 GC 21 (RP 3) 1260 k = true := by kc_cover 64
theorem rec7 : ∀ k < 1008, recC C7 GC 21 (RP 7) 1008 k = true := by kc_cover 64
theorem rec8 : ∀ k < 1008, recC C8 GC 21 (RP 8) 1008 k = true := by kc_cover 64

end CertificateChecks.KernelSpor.Co2Cls

end
