module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Combinatorics.Matroid.Init

public section

namespace CFSG.RankThree.PartOne.KLCE

open Polynomial

@[expose] noncomputable def frobAut (k : Type) [Field k] [Finite k] [CharP k 2] (m : ℕ) :
    k ≃+* k :=
  RingEquiv.ofBijective (iterateFrobenius k 2 m)
    ⟨(iterateFrobenius k 2 m).injective, Finite.injective_iff_surjective.1
      (iterateFrobenius k 2 m).injective⟩

theorem frobAut_apply {k : Type} [Field k] [Finite k] [CharP k 2] (m : ℕ) (x : k) :
    frobAut k m x = x ^ 2 ^ m := rfl

theorem frobAut_ne_one {k : Type} [Field k] [Finite k] [CharP k 2] {n m : ℕ}
    (hk : Nat.card k = 2 ^ n) (hm : 0 < m) (hmn : m < n) : frobAut k m ≠ 1 := by
  intro h
  have : Fintype k := Fintype.ofFinite k
  have hall : ∀ x : k, x ^ 2 ^ m = x := fun x => by
    rw [← frobAut_apply]
    exact DFunLike.congr_fun h x
  have h1m : 1 < 2 ^ m := Nat.one_lt_two_pow hm.ne'
  have hdeg := FiniteField.X_pow_card_sub_X_natDegree_eq k h1m
  have hne : (X ^ 2 ^ m - X : k[X]) ≠ 0 :=
    Polynomial.ne_zero_of_natDegree_gt (n := 0) (by rw [hdeg]; omega)
  have hsub : (Finset.univ : Finset k).val ⊆ (X ^ 2 ^ m - X : k[X]).roots := by
    intro x _
    rw [Polynomial.mem_roots hne]
    simp [Polynomial.IsRoot, hall x]
  have h2 := Polynomial.card_le_degree_of_subset_roots hsub
  rw [hdeg, Finset.card_univ, ← Nat.card_eq_fintype_card, hk] at h2
  exact absurd h2 (not_le.2 (Nat.pow_lt_pow_right (by norm_num) hmn))

end CFSG.RankThree.PartOne.KLCE
