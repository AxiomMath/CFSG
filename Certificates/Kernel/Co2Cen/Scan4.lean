module

public import Certificates.Data.Kernel.Co2Cen
public import Certificates.Kernel.Co2Cls.DS
import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSpor.Co2Cen

open CFSG.KC.Co2Cen CertificateChecks.KernelSpor.Co2Cls CertificateChecks.KernelSpor.Co2Syl

theorem scan24 : ∀ k < 1260,
    scanC C2 (fun _ => 0) (fun _ _ => false) (G4 0) 0 k = true := by kc_cover 64

theorem scan74 : ∀ k < 1008,
    scanC C7 (fun _ => 0) (fun _ _ => false) (G4 0) 0 k = true := by kc_cover 64

end CertificateChecks.KernelSpor.Co2Cen

end
