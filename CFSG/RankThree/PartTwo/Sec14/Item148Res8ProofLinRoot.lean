module

public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec14.Item148Res8

open Matrix

variable {K : Type} [Field K]

theorem commutator_transvection {n : ℕ} {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (s t : K) :
    SpecialLinearGroup.transvection hij s * SpecialLinearGroup.transvection hjk t *
        (SpecialLinearGroup.transvection hij s)⁻¹ * (SpecialLinearGroup.transvection hjk t)⁻¹ =
      SpecialLinearGroup.transvection hik (s * t) := by
  rw [SpecialLinearGroup.transvection_inv, SpecialLinearGroup.transvection_inv]
  apply Subtype.ext
  change (SpecialLinearGroup.transvection hij s : Matrix (Fin n) (Fin n) K) *
      (SpecialLinearGroup.transvection hjk t : Matrix (Fin n) (Fin n) K) *
      (SpecialLinearGroup.transvection hij (-s) : Matrix (Fin n) (Fin n) K) *
      (SpecialLinearGroup.transvection hjk (-t) : Matrix (Fin n) (Fin n) K) =
      (SpecialLinearGroup.transvection hik (s * t) : Matrix (Fin n) (Fin n) K)
  simp only [SpecialLinearGroup.transvection_coe, mul_add, add_mul,
    mul_one, one_mul, single_mul_single_same, single_mul_single_of_ne _ _ _ _ hjk.symm,
    single_mul_single_of_ne _ _ _ _ hij.symm, single_mul_single_of_ne _ _ _ _ hik.symm]
  simp only [zero_mul, add_zero, mul_neg, neg_mul, neg_neg, ← single_neg]
  abel

theorem map_subtype_transvection (F₀ : Subfield K) {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (a : F₀) : SpecialLinearGroup.map F₀.subtype (SpecialLinearGroup.transvection hij a) =
      SpecialLinearGroup.transvection hij (a : K) := by
  apply Subtype.ext
  rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  ext r c
  simp only [Matrix.map_apply, SpecialLinearGroup.transvection_coe, Matrix.add_apply,
    Matrix.one_apply, Matrix.single_apply]
  split_ifs <;> simp

section Dichotomy

variable (H : Subgroup (SpecialLinearGroup (Fin 3) K))

theorem transvection_mem_of_mem_left {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (h1 : SpecialLinearGroup.transvection hjk (1 : K) ∈ H) {a : K}
    (ha : SpecialLinearGroup.transvection hij a ∈ H) :
    SpecialLinearGroup.transvection hik a ∈ H := by
  have := commutator_transvection hij hjk hik a 1
  rw [mul_one] at this
  rw [← this]
  exact H.mul_mem (H.mul_mem (H.mul_mem ha h1) (H.inv_mem ha)) (H.inv_mem h1)

theorem transvection_mem_of_mem_right {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (h1 : SpecialLinearGroup.transvection hij (1 : K) ∈ H) {b : K}
    (hb : SpecialLinearGroup.transvection hjk b ∈ H) :
    SpecialLinearGroup.transvection hik b ∈ H := by
  have := commutator_transvection hij hjk hik 1 b
  rw [one_mul] at this
  rw [← this]
  exact H.mul_mem (H.mul_mem (H.mul_mem h1 hb) (H.inv_mem h1)) (H.inv_mem hb)

@[expose] noncomputable def rootField [Finite K]
    (h1 : ∀ (i j : Fin 3) (hij : i ≠ j), SpecialLinearGroup.transvection hij (1 : K) ∈ H) :
    Subfield K where
  carrier := {a | SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 2) a ∈ H}
  zero_mem' := by
    show SpecialLinearGroup.transvection _ (0 : K) ∈ H
    rw [SpecialLinearGroup.transvection_coeff_zero]
    exact H.one_mem
  one_mem' := h1 0 2 (by decide)
  add_mem' := by
    intro a b ha hb
    show SpecialLinearGroup.transvection _ (a + b) ∈ H
    rw [SpecialLinearGroup.transvection_add]
    exact H.mul_mem ha hb
  neg_mem' := by
    intro a ha
    show SpecialLinearGroup.transvection _ (-a) ∈ H
    rw [← SpecialLinearGroup.transvection_inv]
    exact H.inv_mem ha
  mul_mem' := by
    intro a b ha hb
    have ha' : SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 1) a ∈ H :=
      transvection_mem_of_mem_left H (by decide) (by decide) (by decide) (h1 2 1 (by decide)) ha
    have hb' : SpecialLinearGroup.transvection (by decide : (1 : Fin 3) ≠ 2) b ∈ H :=
      transvection_mem_of_mem_right H (by decide) (by decide) (by decide) (h1 1 0 (by decide)) hb
    show SpecialLinearGroup.transvection _ (a * b) ∈ H
    rw [← commutator_transvection (by decide : (0 : Fin 3) ≠ 1) (by decide : (1 : Fin 3) ≠ 2)]
    exact H.mul_mem (H.mul_mem (H.mul_mem ha' hb') (H.inv_mem ha')) (H.inv_mem hb')
  inv_mem' := by
    intro a ha
    have := Fintype.ofFinite K
    have hpow : ∀ m : ℕ, SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 2) (a ^ m) ∈
        H := by
      intro m
      induction m with
      | zero => rw [pow_zero]; exact h1 0 2 (by decide)
      | succ m ih =>
        have ha' : SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 1) (a ^ m) ∈ H :=
          transvection_mem_of_mem_left H (by decide) (by decide) (by decide) (h1 2 1 (by decide))
            ih
        have hb' : SpecialLinearGroup.transvection (by decide : (1 : Fin 3) ≠ 2) a ∈ H :=
          transvection_mem_of_mem_right H (by decide) (by decide) (by decide)
            (h1 1 0 (by decide)) ha
        rw [pow_succ, ← commutator_transvection (by decide : (0 : Fin 3) ≠ 1)
          (by decide : (1 : Fin 3) ≠ 2)]
        exact H.mul_mem (H.mul_mem (H.mul_mem ha' hb') (H.inv_mem ha')) (H.inv_mem hb')
    by_cases ha0 : a = 0
    · show SpecialLinearGroup.transvection _ (a⁻¹) ∈ H
      rw [ha0, _root_.inv_zero, SpecialLinearGroup.transvection_coeff_zero]
      exact H.one_mem
    · have hq : 2 ≤ Fintype.card K := Fintype.one_lt_card
      have e : a⁻¹ = a ^ (Fintype.card K - 2) := by
        have h1' := FiniteField.pow_card_sub_one_eq_one a ha0
        rw [show Fintype.card K - 1 = (Fintype.card K - 2) + 1 by omega, pow_succ] at h1'
        exact (eq_inv_of_mul_eq_one_left h1').symm
      show SpecialLinearGroup.transvection _ (a⁻¹) ∈ H
      rw [e]
      exact hpow _

theorem rootSet_dichotomy [Finite K] (F₀ : Subfield K) {q : ℕ} (hq : 2 ≤ q)
    (hF₀ : Nat.card F₀ = q) (hK : Nat.card K = q ^ 3)
    (hH : ∀ (i j : Fin 3) (hij : i ≠ j) (a : K), a ∈ F₀ →
      SpecialLinearGroup.transvection hij a ∈ H) :
    (∀ a : K, SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 2) a ∈ H → a ∈ F₀) ∨
      (∀ (i j : Fin 3) (hij : i ≠ j) (a : K), SpecialLinearGroup.transvection hij a ∈ H) := by
  classical
  have h1 : ∀ (i j : Fin 3) (hij : i ≠ j), SpecialLinearGroup.transvection hij (1 : K) ∈ H :=
    fun i j hij => hH i j hij 1 F₀.one_mem
  set S := rootField H h1 with hS
  have hFS : F₀ ≤ S := fun a ha => hH 0 2 (by decide) a ha
  have := Fintype.ofFinite K
  have := Fintype.ofFinite F₀
  have := Fintype.ofFinite S
  let : Algebra F₀ S := (Subfield.inclusion hFS).toAlgebra
  obtain ⟨d, hd⟩ := VectorSpace.card_fintype F₀ S
  obtain ⟨e, he⟩ := VectorSpace.card_fintype S K
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF₀] at hd
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, hd, ← pow_mul] at he
  have hde : 3 = d * e := Nat.pow_right_injective hq he
  have hd3 : d ∣ 3 := ⟨e, hde⟩
  rcases (Nat.prime_three.eq_one_or_self_of_dvd d hd3) with rfl | rfl
  ·
    left
    rw [pow_one] at hd
    have hSF : (F₀ : Set K) = (S : Set K) := by
      refine Set.eq_of_subset_of_ncard_le hFS ?_ (Set.toFinite _)
      rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
      exact (hd.trans hF₀.symm).le
    intro a ha
    have haS : a ∈ (S : Set K) := ha
    rw [← hSF] at haS
    exact haS
  ·
    right
    have hall : ∀ a : K, SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 2) a ∈ H := by
      have hSK : (S : Set K) = Set.univ := by
        refine Set.eq_of_subset_of_ncard_le (Set.subset_univ (S : Set K)) ?_
          (Set.toFinite (Set.univ : Set K))
        rw [Set.ncard_univ, ← Nat.card_coe_set_eq]
        exact (hK.trans hd.symm).le
      intro a
      have : a ∈ (S : Set K) := by rw [hSK]; trivial
      exact this
    have h01 : ∀ a : K, SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 1) a ∈ H :=
      fun a => transvection_mem_of_mem_left H (by decide) (by decide) (by decide)
        (h1 2 1 (by decide)) (hall a)
    have h12 : ∀ a : K, SpecialLinearGroup.transvection (by decide : (1 : Fin 3) ≠ 2) a ∈ H :=
      fun a => transvection_mem_of_mem_right H (by decide) (by decide) (by decide)
        (h1 1 0 (by decide)) (hall a)
    have h21 : ∀ a : K, SpecialLinearGroup.transvection (by decide : (2 : Fin 3) ≠ 1) a ∈ H :=
      fun a => transvection_mem_of_mem_right H (by decide : (2 : Fin 3) ≠ 0) (by decide)
        (by decide) (h1 2 0 (by decide)) (h01 a)
    have h10 : ∀ a : K, SpecialLinearGroup.transvection (by decide : (1 : Fin 3) ≠ 0) a ∈ H :=
      fun a => transvection_mem_of_mem_left H (by decide : (1 : Fin 3) ≠ 2) (by decide)
        (by decide) (h1 2 0 (by decide)) (h12 a)
    have h20 : ∀ a : K, SpecialLinearGroup.transvection (by decide : (2 : Fin 3) ≠ 0) a ∈ H :=
      fun a => transvection_mem_of_mem_right H (by decide : (2 : Fin 3) ≠ 1) (by decide)
        (by decide) (h1 2 1 (by decide)) (h10 a)
    intro i j hij a
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact h01 a
    · exact hall a
    · exact h10 a
    · exact absurd rfl hij
    · exact h12 a
    · exact h20 a
    · exact h21 a
    · exact absurd rfl hij

end Dichotomy

end CFSG.RankThree.PartTwo.Sec14.Item148Res8
