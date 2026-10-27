module

public import Certificates.Kernel.Co2Cen.Data
public import Certificates.Kernel.Co2Cls.DS
import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSpor.Co2Cen

open CFSG.KC.Co2Cen CertificateChecks.KernelSpor.Co2Cls CertificateChecks.KernelSpor.Co2Syl

theorem scan28 : ∀ k < 1260,
    scanC C2 S28 (fun X _ => Nat.beq X (RP 7)) (RP 8) 6 k = true := by kc_cover 64

theorem scan78 : ∀ k < 1008,
    scanC C7 S78 (fun X _ => Nat.beq X (RP 7)) (RP 8) 6 k = true := by kc_cover 64

end CertificateChecks.KernelSpor.Co2Cen

end
