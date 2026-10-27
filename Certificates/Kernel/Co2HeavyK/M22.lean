module

public import Certificates.Kernel.Co2HeavyK.Data
public import Certificates.Kernel.Sporadic.Co2.ChainA
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2HeavyK

open CFSG.KC.Co2HeavyK CFSG.KC.Co2InvS CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
  CertificateChecks.KernelSpor.Co2Inv

theorem inv_ok : invK (MT 0) (MT 1) (MT 2) (MT 3) = true := by quickRfl

theorem rel_ok : relK (MT 0) (MT 1) (MT 2) (MT 3) = true := by quickRfl

theorem vecA : ∀ t < 2300, mvecK VP (MT 4) (MP 0) t = true := by kc_cover 100

theorem vecB : ∀ t < 2300, mvecK VP (MT 5) (MP 1) t = true := by kc_cover 100

theorem permA : invEqK 2300 12 (mask 12) (2300 * 12) (MP 0) (MP 2) = true := by quickRfl

theorem permB : invEqK 2300 12 (mask 12) (2300 * 12) (MP 1) (MP 3) = true := by quickRfl

theorem hiA : Nat.beq (Nat.shiftRight (MP 0) (2300 * 12)) 0 = true := by quickRfl

theorem hiB : Nat.beq (Nat.shiftRight (MP 1) (2300 * 12)) 0 = true := by quickRfl

theorem siftA : siftK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) KernelSpor.Co2A.LR
    KernelSpor.Co2A.TRI KernelSpor.Co2A.BP 6 0 (MP 0) = true := by quickRfl

theorem siftB : siftK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) KernelSpor.Co2A.LR
    KernelSpor.Co2A.TRI KernelSpor.Co2A.BP 6 0 (MP 1) = true := by quickRfl

end CertificateChecks.KernelCo2HeavyK

end
