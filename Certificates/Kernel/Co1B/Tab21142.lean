module

public import Certificates.Data.Kernel.Co1B
public import Certificates.Kernel.Co1B.IotaData
public import Certificates.Kernel.Co1B.Data21142
public import CFSG.Sporadic.Co1Patterson.TwistNativeInputs
import Certificates.Kernel.J4Q.AllN
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977Commuting
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylData
public import CFSG.Sporadic.Co1Block.Iota

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo1B

open CFSG.KC.Co1F2 CFSG.KC.Co1B CFSG.KD.Co1B CFSG.KLie.CT CFSG.Sporadic.Co1Patterson.TwistNative

@[expose] noncomputable def qwT (e : Nat) : Nat :=
  (List.range 8).foldl (fun acc k => if e.testBit k = true then mulK acc (getL oneK IRS (36 + k)) else acc) oneK

@[expose] noncomputable def ypT (c : Nat) : Nat :=
  (List.range 8).foldl (fun acc i => if c.testBit i = true then mulK acc (qwT (yBits.getD i 0)) else acc) oneK

@[expose] noncomputable def ypChk (t : Nat) : Bool := Nat.beq (ypT (getL 0 ALK42 t)) (getL 0 YP42 t)

#j4q_all CFSG.KD.Co1B.YPT42 CertificateChecks.KernelCo1B.ypChk 128

theorem consts_chk : andB (Nat.beq (getL oneK IRS 23) AL42)
    (andB (Nat.beq (qwT 1) W0L42) (Nat.beq (mulK W0L42 AL42) W0AL42)) = true := by
  quickRfl

theorem aList_chk : decide (aList = ALK42.flatMap fun c => [(c, 0), (c, 1)]) = true := by
  quickRfl

end CertificateChecks.KernelCo1B

end
