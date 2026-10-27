module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG

namespace FiveTransitive.CosetCountSaturation

open scoped BigOperators

theorem eq_of_sum_eq
    {A : Type*} [Fintype A] (f : A → ℕ) (b : ℕ)
    (hle : ∀ a, f a ≤ b) (hsum : (∑ a, f a) = Nat.card A * b) :
    ∀ a, f a = b := by
  have h : (∑ a, f a) = ∑ _a : A, b := by
    simpa only [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul,
      Nat.card_eq_fintype_card] using hsum
  exact fun a => (Finset.sum_eq_sum_iff_of_le (fun i _ => hle i)).mp h a (Finset.mem_univ a)

end FiveTransitive.CosetCountSaturation

end CFSG
