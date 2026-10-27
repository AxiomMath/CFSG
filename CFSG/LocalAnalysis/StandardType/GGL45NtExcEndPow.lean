module

public import Mathlib.Algebra.Group.Hom.Defs

public section

namespace CFSG.HardMathSupport.C14Exc

@[expose] def endPow {G : Type*} [Monoid G] (S : G →* G) (n : ℕ) : G →* G :=
  @HPow.hPow (Monoid.End G) ℕ (Monoid.End G) _ S n

theorem endPow_apply {G : Type*} [Monoid G] (S : G →* G) (n : ℕ) (x : G) :
    endPow S n x = S^[n] x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    have h : (@HPow.hPow (Monoid.End G) ℕ (Monoid.End G) _ S (n + 1)) =
        (@HPow.hPow (Monoid.End G) ℕ (Monoid.End G) _ S n) * (show Monoid.End G from S) :=
      pow_succ _ _
    change (@HPow.hPow (Monoid.End G) ℕ (Monoid.End G) _ S (n + 1)) x = _
    rw [h]
    exact ih (S x)

end CFSG.HardMathSupport.C14Exc
