module

public import Certificates.Kernel.Co2Cen.Data
public import Certificates.Kernel.Co2Cls.DS
public import Certificates.Kernel.Co2JRank.Data
import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSpor.Co2Cen

open CFSG.KC.Co2Cen CertificateChecks.KernelSpor.Co2Cls CertificateChecks.KernelSpor.Co2Syl

theorem scan21 : ∀ k < 1260,
    scanC C2 S21 (exW Co2JRank.WG 5) (RP 1) 8 k = true := by kc_cover 64

theorem scan71 : ∀ k < 1008,
    scanC C7 S71 (exW Co2JRank.WG 5) (RP 1) 8 k = true := by kc_cover 64

end CertificateChecks.KernelSpor.Co2Cen

end
