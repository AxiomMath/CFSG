module

public import CFSG.OddTranspositions.O4Minus5Pair

public section

namespace CFSG.OddTranspositions.QZ

local instance factPrimeFiveField : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

open Polynomial

noncomputable section

theorem pow_five_eq_self_iff (a : K25) :
    a ^ 5 = a ↔ ∃ x : ZMod 5, algebraMap (ZMod 5) K25 x = a := by
  classical
  haveI : Fintype K25 := Fintype.ofFinite K25
  haveI : DecidableEq K25 := Classical.decEq K25
  let g : ZMod 5 → K25 := algebraMap (ZMod 5) K25
  have hg_inj : Function.Injective g := (algebraMap (ZMod 5) K25).injective
  have hdeg : (X ^ 5 - X : K25[X]).natDegree = 5 := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
    · exact Polynomial.natDegree_X_pow 5
    · rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X]
      norm_num
  have hp0 : (X ^ 5 - X : K25[X]) ≠ 0 := by
    intro hp
    have := hdeg
    rw [hp, Polynomial.natDegree_zero] at this
    omega
  have hroots_card : (X ^ 5 - X : K25[X]).roots.toFinset.card ≤ 5 := by
    calc (X ^ 5 - X : K25[X]).roots.toFinset.card ≤ (X ^ 5 - X : K25[X]).roots.card :=
          Multiset.toFinset_card_le _
      _ ≤ (X ^ 5 - X : K25[X]).natDegree := Polynomial.card_roots' _
      _ = 5 := hdeg
  constructor
  · intro ha
    have hroot : (X ^ 5 - X : K25[X]).IsRoot a := by
      rw [Polynomial.IsRoot, eval_sub, eval_pow, eval_X, sub_eq_zero]
      exact ha
    have hsub : (Finset.univ.image g) ⊆ (X ^ 5 - X : K25[X]).roots.toFinset := by
      intro y hy
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hy
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0]
      rw [Polynomial.IsRoot, eval_sub, eval_pow, eval_X, sub_eq_zero]
      have hx : x ^ 5 = x := by
        have := FiniteField.pow_card x
        simpa using this
      rw [← map_pow, hx]
    have himg_card : (Finset.univ.image g).card = 5 := by
      rw [Finset.card_image_of_injective _ hg_inj, Finset.card_univ]
      norm_num [ZMod.card]
    have heq : Finset.univ.image g = (X ^ 5 - X : K25[X]).roots.toFinset := by
      apply Finset.eq_of_subset_of_card_le hsub
      rw [himg_card]
      exact hroots_card
    have ha_mem : a ∈ (X ^ 5 - X : K25[X]).roots.toFinset := by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0]
      exact hroot
    rw [← heq] at ha_mem
    obtain ⟨x, -, hx⟩ := Finset.mem_image.mp ha_mem
    exact ⟨x, hx⟩
  · rintro ⟨x, rfl⟩
    have hx : x ^ 5 = x := by
      have := FiniteField.pow_card x
      simpa using this
    rw [← map_pow, hx]

end

end CFSG.OddTranspositions.QZ
