module

public import Certificates.Kernel.Co1ThreeK.DataC
public import Certificates.Data.Kernel.Co1Three.Cen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1ThreeK

open CFSG.KC.Enum CFSG.KC.Co1Cl CFSG.KC.Co1F2

theorem kCen : (Nat.beq CB.B.length 26 && allN 26 (fun l => Nat.beq (lenL (getLL CB.B l)) 3 &&
    fixFreeK (getLL CS.TR (Nat.succ l)) (getLL CB.B l))) = true := by quickRfl

theorem kR0 : (Nat.blt 0 CB.K0 && Nat.blt CB.K0 27 && Nat.beq (lenL CB.B0) 4 &&
    fixFreeK (getLL CS.TR CB.K0) CB.B0) = true := by quickRfl

end CertificateChecks.KernelCo1ThreeK

end
