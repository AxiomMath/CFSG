module

public import Certificates.Data.Kernel.SporSch.MathieuOC2

public section

namespace CFSG.KS.SporSch.MOC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.M11

@[expose] noncomputable def ptPow (w m y : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun i => i) (fun _ ih i => ih (pg w m y i))

@[expose] noncomputable def fixPt (w m idn y e i : Nat) : Bool :=
  Nat.beq (ptPow w m y e i) (pg w m idn i)

@[expose] noncomputable def cntWord2F (n w m nw idn : Nat) (LR TR : Nat → Nat) (nb mx my : Nat)
    (ws : List (List Nat × Nat)) (R k₀ k₁ : Nat) : Nat :=
  enumFrom n w m nw LR TR (fun y => bAnd(fixPt w m idn y (Nat.succ (Nat.sub my (nat_lit 1)))
      (nat_lit 0), bAnd(fixPt w m idn y (Nat.succ (Nat.sub my (nat_lit 1))) (nat_lit 1),
      bAnd(ordIs n w m idn y (Nat.sub my (nat_lit 1)), wordOrdK n w m idn mx my ws R y))))
    (Nat.sub nb (nat_lit 2)) (nat_lit 2) (start2 n w m nw LR TR idn k₀ k₁) (nat_lit 0)

end CFSG.KS.SporSch.MOC

end
