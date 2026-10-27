module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Data.Set.Card

public section

namespace CFSG

open AddMonoidAlgebra
open scoped Pointwise

namespace BurnsideSchur

variable {R C : Type*} [CommRing R] [Fintype C]

variable (R) in
noncomputable def ofSet (S : Set C) : AddMonoidAlgebra R C :=
  ∑ x, single x (S.indicator 1 x)

@[simp]
theorem coeff_ofSet (S : Set C) (x : C) : (ofSet R S).coeff x = S.indicator 1 x := by
  classical
  simp [ofSet, coeff_sum, Finsupp.single_apply]

variable [AddCommGroup C]

theorem coeff_mul_eq_sum (a b : AddMonoidAlgebra R C) (c : C) :
    (a * b).coeff c = ∑ x, a.coeff x * b.coeff (c - x) := by
  rw [coeff_mul_apply_left, Finsupp.sum_fintype _ _ (by simp)]
  simp [sub_eq_neg_add]

theorem coeff_ofSet_mul_ofSet (A B : Set C) (c : C) :
    (ofSet R A * ofSet R B).coeff c = ((A ∩ (c +ᵥ -B)).ncard : R) := by
  classical
  rw [coeff_mul_eq_sum, Set.ncard_eq_toFinset_card', ← Set.filter_mem_univ_eq_toFinset,
    Finset.card_filter, Nat.cast_sum]
  refine Fintype.sum_congr _ _ fun x => ?_
  by_cases hx : x ∈ A <;> by_cases hcx : c - x ∈ B <;>
    simp [Set.mem_vadd_set_iff_neg_vadd_mem, hx, hcx, neg_add_eq_sub]

theorem coeff_ofSet_pow_char (p : ℕ) [Fact p.Prime] [CharP R p] (S : Set C) (c : C) :
    (ofSet R S ^ p).coeff c = ({x ∈ S | p • x = c}.ncard : R) := by
  classical
  have : CharP (AddMonoidAlgebra R C) p :=
    charP_of_injective_ringHom (f := singleZeroRingHom)
      (fun a b h => by simpa using congrArg (fun x => x.coeff 0) h) p
  rw [ofSet, sum_pow_char, Set.ncard_eq_toFinset_card', ← Set.filter_mem_univ_eq_toFinset,
    Finset.card_filter, Nat.cast_sum, coeff_sum, Finsupp.finsetSum_apply]
  refine Fintype.sum_congr _ _ fun x => ?_
  by_cases hx : x ∈ S <;> by_cases hpx : p • x = c <;>
    simp [single_pow, hx, hpx, (Fact.out : p.Prime).ne_zero]

end BurnsideSchur

end CFSG
