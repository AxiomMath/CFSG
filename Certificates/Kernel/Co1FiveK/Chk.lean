module

public import Certificates.Kernel.Co1FiveK.Data
public import Certificates.Kernel.SporSch.Co1.Packed
public import Certificates.Data.Kernel.Co1FiveK
public import Certificates.Data.Kernel.SporSch.Co1MatW
public import Certificates.Data.CFSGNative.Timmesfeld.Co1Five
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1FiveK

open CFSG.KC.Enum CFSG.KS.SporSch.M24 CFSG.KC.Co1FiveK Timmesfeld.Co1Five
open CFSG.KC.Co1B (mulWK)
open CFSG.KC.Co1F2 (getL)

@[expose] noncomputable def QM (l : Nat) : Nat := D.M (Nat.add (nat_lit 67) l)

@[expose] noncomputable def DK (i : Nat) : Nat := D.M (Nat.add (nat_lit 70) i)

@[expose] noncomputable def AT (k : Nat) : Nat := getL (nat_lit 0) FW.AT k

@[expose] noncomputable def PG (τ l : Nat) : Nat :=
  nIf(Nat.beq l (nat_lit 0), a0K DK (repA.getD τ 0), a0K DK (repB.getD τ 0))

theorem kBase : (Nat.beq (D.M 0) CertificateChecks.KernelSporSch.Co1Packed.PA &&
    Nat.beq (D.M 1) CertificateChecks.KernelSporSch.Co1Packed.PB) = true := by quickRfl

theorem kD : dagWK D.M D.MI 2 137 dagWords = true := by quickRfl

theorem kQN : Nat.beq QT.N 625 = true := by quickRfl

theorem kQ : gtPinK QM 3 100000 QT.N QT.P QT.PAR QT.LAB QT.W QT.S = true := by quickRfl

theorem kQ5 : allN 625 (fun i => Nat.beq (pwK (QT.P i) 5) idM) = true := by quickRfl

theorem kA0 : allN 3 (fun i => bAnd(Nat.beq (pwK (DK i) 5) idM,
    allN 3 fun j => Nat.beq (mulWK (DK i) (DK j)) (mulWK (DK j) (DK i)))) = true := by quickRfl

theorem kAT : allN 125 (fun k => Nat.beq (AT k) (a0K DK k)) = true := by quickRfl

theorem kATd : allN 125 (fun a => allN a fun b => !CFSG.KC.Co1End.eqK (AT a) (AT b)) = true := by
  quickRfl

theorem kFus : allN 625 (fun i => strictB (getL (nat_lit 0) FW.W i) fun c =>
    bIf(Nat.blt c 125, Nat.beq (QT.P i) (AT c),
      strictB (Nat.mod (Nat.sub c 125) 20) fun j => strictB (Nat.div (Nat.sub c 125) 20) fun y =>
        bAnd(Nat.blt y 625, Nat.beq (QT.P i)
          (mulWK (mulWK (QT.P y) (D.M (Nat.add 73 j))) (pwK (QT.P y) 4))))) = true := by
  quickRfl

theorem kConj : allN 20 (fun j => strictB (getL (nat_lit 0) FW.C j) fun k => bAnd(Nat.blt k 125,
    Nat.beq (mulWK (mulWK (D.M (Nat.add 93 j)) (D.M (Nat.add 73 j))) (D.MI (Nat.add 93 j))) (AT k)))
    = true := by
  quickRfl

@[expose] def numP (p : Nat) : Bool :=
  decide (planeT.getD p 0 < 3) && decide (planeA.getD p 0 < 125) &&
    decide (planeB.getD p 0 < 125) &&
    dot5 (planeF.getD p []) (digitsOf (planeA.getD p 0)) == 0 &&
    dot5 (planeF.getD p []) (digitsOf (planeB.getD p 0)) == 0 &&
    (List.range 5).all (fun k => digitsOf (planeB.getD p 0) != scale5 k (digitsOf (planeA.getD p 0)))

@[expose] noncomputable def conjP (p : Nat) : Bool :=
  strictB (idxPC.getD p 0) fun c => bAnd(Nat.blt c 137,
    bAnd(Nat.beq (mulWK (mulWK (D.M c) (a0K DK (repA.getD (planeT.getD p 0) 0))) (D.MI c))
      (a0K DK (planeA.getD p 0)),
      Nat.beq (mulWK (mulWK (D.M c) (a0K DK (repB.getD (planeT.getD p 0) 0))) (D.MI c))
        (a0K DK (planeB.getD p 0))))

theorem kPl : allN 31 (fun p => bAnd(numP p, conjP p)) = true := by quickRfl

theorem kCov : ((List.range 125).all fun k => k == 0 ||
    (List.range 31).any fun p => (List.range 5).any fun c =>
      decide (1 ≤ c) && (digitsOf k == scale5 c (planeF.getD p [] |>.getD 0 0,
        planeF.getD p [] |>.getD 1 0, planeF.getD p [] |>.getD 2 0))) = true := by
  quickRfl

theorem kRep : (List.range 3).all (fun τ => decide (repA.getD τ 0 < 125) && decide (repB.getD τ 0 < 125))
    = true := by
  quickRfl

theorem kPTN : (Nat.beq PT0.N 25 && Nat.beq PT1.N 25 && Nat.beq PT2.N 25) = true := by quickRfl

theorem kPT0 : gtPinK (PG 0) 2 100000 PT0.N PT0.P PT0.PAR PT0.LAB PT0.W PT0.S = true := by quickRfl

theorem kPT1 : gtPinK (PG 1) 2 100000 PT1.N PT1.P PT1.PAR PT1.LAB PT1.W PT1.S = true := by quickRfl

theorem kPT2 : gtPinK (PG 2) 2 100000 PT2.N PT2.P PT2.PAR PT2.LAB PT2.W PT2.S = true := by quickRfl

end CertificateChecks.KernelCo1FiveK

end
