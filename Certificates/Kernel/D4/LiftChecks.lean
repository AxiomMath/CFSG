module

public import Certificates.Kernel.D4.ChainAD
public import Certificates.Kernel.D4.Hex
public import Certificates.Kernel.D4.EnumQ
public import Certificates.Kernel.D4.EnumS0
public import Certificates.Kernel.D4.RowHex
public import Certificates.Kernel.D4.PhiData
public import Certificates.Data.Kernel.D4LiftK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelD4

open CFSG.KC.Enum CFSG.KS CFSG.KC.Misc.ArrEnum CFSG.KC.D4Lift

theorem bS : allN 4 (fun j => Nat.beq (ES.G j) (HX.F j)) = true ∧
    Nat.beq (ES.G 4) (RX.F 0) = true ∧ Nat.beq ES.ng 5 = true ∧ Nat.beq ES.N 243 = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

theorem liftOK : liftK 2457 12 CA.LR CA.TRI CA.BP 7 (RX.F 0) (PH 0) EQ.N EQ.T 48
    (fun j => RX.F (Nat.add 1 j)) ES.N ES.T = true := by quickRfl

end CertificateChecks.KernelD4

end
