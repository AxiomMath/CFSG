module

public import CFSG.GH74.GLS.C3.Layer2.L5C2c
public import CFSG.GH74.GLS.C3.Layer2.L5C2a

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5.Fus

variable {n : Nat} [Group (Idx n)]

@[expose] def ordGo (a : Idx n) : Nat → Idx n → Nat → Nat
  | 0, _, _ => 0
  | fuel + 1, x, k => if x = 1 then k else ordGo a fuel (x * a) (k + 1)

@[expose] def ordI (a : Idx n) : Nat := ordGo a n a 1

@[expose] def ivB (ci : Array Nat) (ld : List Nat) (u : Idx n) : Nat :=
  if isInv u then blkOf ci ld u + 1 else 0

@[expose] def tau (ci : Array Nat) (ld : List Nat) (t a : Idx n) : Nat × Nat × Nat × Nat :=
  (ordI a, ivB ci ld (a ^ (ordI a / 2)), ordI (a * t), ivB ci ld ((a * t) ^ (ordI (a * t) / 2)))

@[expose] def scpRefute (ci : Array Nat) (ld : List Nat) (t tp : Idx n) (L : List (Idx n))
    (τ₀ : Nat × Nat × Nat × Nat) : Bool :=
  decide (((elemsI n).filter fun b => decide (b * tp = tp * b) && decide (tau ci ld tp b = τ₀)).length <
    (L.filter fun a => decide (tau ci ld t a = τ₀)).length)

end CFSG.GH74.GLS.C3.Layer2.L5.Fus

end
