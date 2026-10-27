module

public import Certificates.Data.Kernel.SporSch.Co1Elem

public section

namespace CFSG.KC.Co1End

open CFSG.KS.SporSch.M24

@[expose] noncomputable def eqK (X Y : Nat) : Bool :=
  Nat.beq (Nat.mod X (Nat.pow 2 576)) (Nat.mod Y (Nat.pow 2 576))

@[expose] noncomputable def commK (X Y : Nat) : Bool := eqK (mulK X Y) (mulK Y X)

@[expose] noncomputable def notInK (x : Nat) (L : List Nat) : Bool := L.all fun y => !eqK y x

@[expose] noncomputable def fourK (a b : Nat) : List Nat := [idM, a, b, mulK a b]

@[expose] noncomputable def swapK (A e c₁ c₂ E2 : Nat) : Bool :=
  eqK e E2 && eqK (mulK A A) idM && eqK (mulK e e) idM && commK A e &&
    notInK A [idM] && notInK e [idM, A] &&
    commK c₁ A && eqK (mulK c₁ e) (mulK (mulK A e) c₁) &&
    commK c₂ e && eqK (mulK c₂ A) (mulK (mulK A e) c₂)

@[expose] noncomputable def conjOKK (A e f₁ f₂ g₁ g₂ : Nat) (db : List Nat) : Bool :=
  commK f₁ A && commK f₁ e && commK f₂ A && commK f₂ e && notInK f₁ (fourK A e) &&
    eqK g₁ (mulK ((fourK A e).getD (db.getD 0 0) idM) ((fourK f₁ f₂).getD (db.getD 1 0) idM)) &&
    eqK g₂ (mulK ((fourK A e).getD (db.getD 2 0) idM) ((fourK f₁ f₂).getD (db.getD 3 0) idM)) &&
    notInK g₁ (fourK A e) && notInK g₁ (fourK f₁ f₂)

@[expose] noncomputable def elemK (A X Y e c₁ c₂ a ai b bi : Nat) (db : List Nat) : Bool :=
  swapK A e c₁ c₂ (powK (mulK X Y) 13) && eqK (mulK a ai) idM && eqK (mulK b bi) idM &&
    conjOKK A e (mulK (mulK a A) ai) (mulK (mulK a e) ai) (mulK (mulK b A) bi)
      (mulK (mulK b e) bi) db

end CFSG.KC.Co1End

end
