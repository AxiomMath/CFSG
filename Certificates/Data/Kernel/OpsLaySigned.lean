module

public import Certificates.Data.Kernel.OpsV4
public import CFSG.LocalAnalysis.SectionRank.QTK.CoverBSignedCheck
public import Certificates.Data.DoubleCoverRanks
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.KC.OpsLaySigned

open CFSG.SectionRank.Native CFSG.SectionRank.QTK.CoverB CFSG.RankThree.PartTwo.Census
  CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanks.Native CFSG.KC.LQT CFSG.KC.OpsLayK
  CFSG.KC.OpsV4

variable {V : Type}

@[expose] noncomputable def signedG (O : Ops Nat V) (D : SignedData) (g : Nat → Nat) : Bool :=
  [D.t₁, D.t₂, D.a, D.b, D.d₁, D.d₂].all (decide <| · < D.base.nregs) &&
    O.elemOK [g D.a, g D.b] D.base.tests &&
    O.eq (O.mul (g D.t₁) (g D.t₁)) O.one && O.eq (O.mul (g D.t₂) (g D.t₂)) O.one &&
    O.commOK (g D.t₁) (g D.t₂) &&
    D.base.tests.any (fun k => O.vne (O.vmul (O.unit k) (g D.t₁)) (O.unit k)) &&
    V4Data.conjOK O (g D.a) (g D.t₁) (g D.t₁) (g D.t₂) &&
    V4Data.conjOK O (g D.a) (g D.t₂) (g D.t₁) (g D.t₂) &&
    V4Data.conjOK O (g D.b) (g D.t₁) (g D.t₁) (g D.t₂) &&
    V4Data.conjOK O (g D.b) (g D.t₂) (g D.t₁) (g D.t₂) &&
    O.eq (O.mul (g D.d₁) (g D.d₁)) O.one && O.eq (O.mul (g D.d₂) (g D.d₂)) O.one &&
    O.eq (O.mul (g D.d₁) (g D.a)) (O.mul (O.mul (g D.a) (g D.a)) (g D.d₁)) &&
    O.commOK (g D.d₁) (g D.b) &&
    O.eq (O.mul (g D.d₂) (g D.b)) (O.mul (O.mul (g D.b) (g D.b)) (g D.d₂))

@[expose] noncomputable def signedK (c : Lay) (A B : Nat) (D : SignedData) : Bool :=
  progOK D.base.nregs D.base.prog && D.base.tests.all (decide <| · < c.d) &&
    runC c D.base.prog (initR c A B D.base.nregs) fun R => signedG (opsL c) D (getR c R)

@[expose] noncomputable def e8G (O : Ops Nat V) (pw : Nat → Nat → Nat) (D : E8Data)
    (g : Nat → Nat) : Bool :=
  strictB (pw (g D.rh) (D.oh - 1)) fun H' =>
  strictB (O.mul (O.mul (g D.rh) (g D.rx)) H') fun X₂ =>
  strictB (O.mul (O.mul (g D.rh) X₂) H') fun X₃ =>
    O.eq (pw (g D.rx) 2) O.one && O.eq (pw (g D.rh) D.oh) O.one &&
      O.vne (O.vmul (O.unit D.t) (g D.rx)) (O.unit D.t) &&
      O.eq (O.mul (g D.rx) X₂) (O.mul X₂ (g D.rx)) &&
      O.eq (O.mul (g D.rx) X₃) (O.mul X₃ (g D.rx)) &&
      O.conjOK (g D.rh) X₃ (O.mul (g D.rx) X₂)

@[expose] noncomputable def e8K3 (c : Lay) (A B : Nat) (D : E8Data) : Bool :=
  progOK D.nregs D.prog && decide (D.rx < D.nregs) && decide (D.rh < D.nregs) &&
    decide (0 < D.oh) && decide (D.oh < 65536) && decide (D.t < c.d) &&
    runC c D.prog (initR c A B D.nregs) fun R => e8G (opsL c) (powK c) D (getR c R)

end CFSG.KC.OpsLaySigned

end
