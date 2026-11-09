module

public import Certificates.Data.Kernel.SporSch.OddConj

public section

namespace CFSG.KS.SporSch.MOC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def oFpw (w m y k x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) x (fun _ ih => pg w m y ih) k

@[expose] noncomputable def oFwalk (w m y x0 : Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => nat_lit 0)
    (fun _ ih t cur => strictN (pg w m y cur) fun nx => nIf(Nat.beq nx x0, t, ih (Nat.succ t) nx))

@[expose] noncomputable def oFfix (n w m y e x : Nat) : Bool :=
  strictB (oFwalk w m y x n (nat_lit 1) x) fun L =>
    Nat.beq (oFpw w m y (nIf(Nat.beq L (nat_lit 0), e, Nat.mod e L)) x) x

@[expose] noncomputable def oFone (n w m y e : Nat) : Bool := allN n (oFfix n w m y e)

@[expose] noncomputable def oFanyWit (n w m e : Nat) (ws : List (Nat × Nat)) (y : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun pr _ ih => Prod.rec (motive := fun _ => Bool)
    (fun c ci => bIf(oFone n w m (pcomp n w m y (pcomp n w m c (pcomp n w m y ci))) e, ih, true))
    pr) ws

@[expose] noncomputable def oFbad (n w m idn e : Nat) (ws : List (Nat × Nat)) (y : Nat) : Bool :=
  bIf(Nat.beq y idn, false, bIf(oFone n w m y e, bIf(oFanyWit n w m e ws y, false, true), false))

@[expose] noncomputable def cntOddFixK (n w m nw idn : Nat) (LR TR : Nat → Nat) (nb e : Nat)
    (ws : List (Nat × Nat)) (k₀ k₁ : Nat) : Nat :=
  enumFrom n w m nw LR TR (oFbad n w m idn e ws) (Nat.sub nb (nat_lit 2)) (nat_lit 2)
    (start2 n w m nw LR TR idn k₀ k₁) (nat_lit 0)

end CFSG.KS.SporSch.MOC

end
