module

public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallCheckV
public import Mathlib.Data.List.Basic

public section

namespace CFSG.KC.ONanSmall

open CFSG.ClassicalInvolution.Q3.TA3.Check

variable {M : Type*} [Group M] [DecidableEq M]

@[expose] def edgeK (K : List M) (t a b : M) : Bool :=
  K.all fun s => !((q8B t a b).all fun r => decide (r * s = s * r)) || memB (q8B t a b) s

@[expose] def pairsVK (B : ℕ) (LN K : List M) (e3b : Bool) (t : M) (C : List M) : Bool :=
  (C.filter fun a => decide (a * a = t)).all fun a =>
    (C.filter fun b => decide (b * b = t)).all fun b =>
      !decide (b * a = t * a * b) ||
      !(C.all fun c => memB (q8B t a b) (c * a * c⁻¹) && memB (q8B t a b) (c * b * c⁻¹)) ||
      (memB LN a && memB LN b) ||
      (C.any fun x => decide (x ^ 3 = 1) && !decide (x * a = a * x ∧ x * b = b * x) &&
        C.all fun y => !decide (y * a = a * y ∧ y * b = b * y) || decide (x * y = y * x)) ||
      (edgeK K t a b && (e3b || noActs3B B C a b))

end CFSG.KC.ONanSmall
