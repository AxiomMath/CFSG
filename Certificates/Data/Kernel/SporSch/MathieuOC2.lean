module

public import Certificates.Data.Kernel.SporSch.MathieuOC

public section

namespace CFSG.KS.SporSch.MOC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.M11

@[expose] noncomputable def start2 (n w m nw : Nat) (LR TR : Nat → Nat) (g₀ k₀ k₁ : Nat) : Nat :=
  strictN (LR (nat_lit 0)) (fun R0 => strictN (LR (nat_lit 1)) (fun R1 =>
    pcomp n w m (pcomp n w m g₀ (TR (Nat.add (roff n nw R0) k₀))) (TR (Nat.add (roff n nw R1) k₁))))

@[expose] noncomputable def cntCommK (n w m nw : Nat) (LR TR : Nat → Nat) (nb g₀ A B k₀ k₁ : Nat) :
    Nat :=
  enumFrom n w m nw LR TR (fun g => bAnd(Nat.beq (pcomp n w m g A) (pcomp n w m A g),
      Nat.beq (pcomp n w m g B) (pcomp n w m B g)))
    (Nat.sub nb (nat_lit 2)) (nat_lit 2) (start2 n w m nw LR TR g₀ k₀ k₁) (nat_lit 0)

@[expose] noncomputable def cntOrd2K (n w m nw idn : Nat) (LR TR : Nat → Nat) (nb g₀ e k₀ k₁ : Nat) :
    Nat :=
  enumFrom n w m nw LR TR (fun g => ordIs n w m idn g (Nat.sub e (nat_lit 1)))
    (Nat.sub nb (nat_lit 2)) (nat_lit 2) (start2 n w m nw LR TR g₀ k₀ k₁) (nat_lit 0)

@[expose] noncomputable def cntWord2K (n w m nw idn : Nat) (LR TR : Nat → Nat) (nb mx my : Nat)
    (ws : List (List Nat × Nat)) (R k₀ k₁ : Nat) : Nat :=
  enumFrom n w m nw LR TR (fun y => bAnd(ordIs n w m idn y (Nat.sub my (nat_lit 1)),
      wordOrdK n w m idn mx my ws R y))
    (Nat.sub nb (nat_lit 2)) (nat_lit 2) (start2 n w m nw LR TR idn k₀ k₁) (nat_lit 0)

end CFSG.KS.SporSch.MOC

end
