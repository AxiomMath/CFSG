module

public import CFSG.RankThree.PartOne.TAIL.LSideModel

public section

namespace CFSG.RankThree.PartOne.TAIL

open Matrix Subgroup
open CFSG.RankThree.PartOne.MB3 (D2 D2_injective coe_D2 bd2 bd2_mul bd2_det)

section Normalizer

theorem mem_normalizer_of_conj_mem' {M : Type*} [Group M] [Finite M] {B : Subgroup M} {w : M}
    (h : ∀ b ∈ B, w * b * w⁻¹ ∈ B) : w ∈ Subgroup.normalizer (B : Set M) := by
  have hle : B.map (MulAut.conj w).toMonoidHom ≤ B := by
    rintro _ ⟨b, hb, rfl⟩
    exact h b hb
  have hcard : Nat.card B ≤ Nat.card (B.map (MulAut.conj w).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj w).injective]
  have heq : B.map (MulAut.conj w).toMonoidHom = B :=
    Subgroup.eq_of_le_of_card_ge hle hcard
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h x hx, fun hx => ?_⟩
  have hx' : w * x * w⁻¹ ∈ B.map (MulAut.conj w).toMonoidHom := by rw [heq]; exact hx
  obtain ⟨b, hb, hbx⟩ := hx'
  have : b = x := by
    have h1 : w * b * w⁻¹ = w * x * w⁻¹ := hbx
    simpa using h1
  exact this ▸ hb

end Normalizer

section Swap

variable {κ : Type} [Fintype κ] [DecidableEq κ]

@[expose] def swM : Matrix ((Fin 3 ⊕ Fin 3) ⊕ κ) ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2) := bd2 0 1 1 0

theorem swM_mul_swM : (swM : Matrix ((Fin 3 ⊕ Fin 3) ⊕ κ) ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)) *
    swM = 1 := by
  rw [swM, bd2_mul]
  simp [bd2]

theorem swM_det : (swM : Matrix ((Fin 3 ⊕ Fin 3) ⊕ κ) ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)).det = 1 := by
  have h : (swM : Matrix ((Fin 3 ⊕ Fin 3) ⊕ κ) ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)).det *
      (swM : Matrix ((Fin 3 ⊕ Fin 3) ⊕ κ) ((Fin 3 ⊕ Fin 3) ⊕ κ) (ZMod 2)).det = 1 := by
    rw [← Matrix.det_mul, swM_mul_swM, Matrix.det_one]
  have key : ∀ d : ZMod 2, d * d = 1 → d = 1 := by decide
  exact key _ h

@[expose] def sw : SLX κ := ⟨swM, swM_det⟩

theorem sw_mul_D2 (P Q : SpecialLinearGroup (Fin 3) (ZMod 2)) :
    (sw : SLX κ) * D2 (P, Q) = D2 (Q, P) * sw := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_D2, coe_D2]
  show swM * bd2 _ 0 0 _ = bd2 _ 0 0 _ * swM
  rw [swM, bd2_mul, bd2_mul]
  simp

theorem sw_conj_eB (i j : ℤ) : (sw : SLX κ) * eB κ i j * sw⁻¹ = eB κ j i := by
  rw [eB_eq_D2, eB_eq_D2, mul_inv_eq_iff_eq_mul, sw_mul_D2]

theorem x1_conj_eB (i j : ℤ) : (x1 : SLX κ) * eB κ i j * x1⁻¹ = eB κ (2 * i) j := by
  rw [eB_eq_D2, eB_eq_D2, x1, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  simp [nSL_conj_zpow]

end Swap

section B0

variable {κ : Type} [Fintype κ] [DecidableEq κ]

@[expose] def B0 (κ : Type) [Fintype κ] [DecidableEq κ] : Subgroup (SLX κ) where
  carrier := {y | ∃ i j : ℤ, y = eB κ i j}
  one_mem' := ⟨0, 0, eB_zero.symm⟩
  mul_mem' := by
    rintro _ _ ⟨i, j, rfl⟩ ⟨i', j', rfl⟩
    exact ⟨i + i', j + j', eB_mul i j i' j'⟩
  inv_mem' := by
    rintro _ ⟨i, j, rfl⟩
    exact ⟨-i, -j, eB_inv i j⟩

theorem eB_mem_B0 (i j : ℤ) : eB κ i j ∈ B0 κ := ⟨i, j, rfl⟩

theorem card_B0 : Nat.card (B0 κ) = 49 := by
  let f : ZMod 7 × ZMod 7 → B0 κ := fun p => ⟨eB κ (p.1.val : ℤ) (p.2.val : ℤ), eB_mem_B0 _ _⟩
  have hf : Function.Bijective f := by
    constructor
    · intro p q h
      have h1 := Subtype.ext_iff.1 h
      simp only [f] at h1
      rw [eB_eq_iff] at h1
      obtain ⟨h2, h3⟩ : p.1 = q.1 ∧ p.2 = q.2 := by simpa using h1
      exact Prod.ext h2 h3
    · rintro ⟨y, i, j, rfl⟩
      refine ⟨((i : ZMod 7), (j : ZMod 7)), ?_⟩
      apply Subtype.ext
      show eB κ (((i : ZMod 7).val : ℕ) : ℤ) (((j : ZMod 7).val : ℕ) : ℤ) = eB κ i j
      rw [eB_eq_iff]
      simp
  rw [← Nat.card_congr (Equiv.ofBijective f hf)]
  simp

theorem x1_mem_normalizer : (x1 : SLX κ) ∈ Subgroup.normalizer (B0 κ : Set (SLX κ)) :=
  mem_normalizer_of_conj_mem' (by
    rintro _ ⟨i, j, rfl⟩
    exact ⟨2 * i, j, (x1_conj_eB i j)⟩)

theorem sw_mem_normalizer : (sw : SLX κ) ∈ Subgroup.normalizer (B0 κ : Set (SLX κ)) :=
  mem_normalizer_of_conj_mem' (by
    rintro _ ⟨i, j, rfl⟩
    exact ⟨j, i, (sw_conj_eB i j)⟩)

theorem zmod7_case_one : ∀ i j m : ZMod 7, i ≠ 0 → j ≠ 0 → 2 * i = m * i → j = m * j → False := by
  decide

theorem zmod7_case_two : ∀ i j m : ZMod 7, i ≠ 0 → j = 0 → j = m * i → i = m * j → False := by
  decide

theorem zmod7_case_three : ∀ i j m : ZMod 7, i = 0 → j ≠ 0 → j = m * i → i = m * j → False := by
  decide

theorem irreducible_B0 : ∀ d ∈ B0 κ, d ≠ 1 →
    ∃ g ∈ Subgroup.normalizer (B0 κ : Set (SLX κ)), g * d * g⁻¹ ∉ Subgroup.zpowers d := by
  rintro _ ⟨i, j, rfl⟩ hd
  have hd' : ¬ ((i : ZMod 7) = 0 ∧ (j : ZMod 7) = 0) := by
    rintro ⟨hi, hj⟩
    apply hd
    rw [← eB_zero, eB_eq_iff]
    simpa using ⟨hi, hj⟩
  by_cases hi : (i : ZMod 7) = 0
  · have hj : (j : ZMod 7) ≠ 0 := fun hj => hd' ⟨hi, hj⟩
    refine ⟨sw, sw_mem_normalizer, ?_⟩
    rw [sw_conj_eB, Subgroup.mem_zpowers_iff]
    rintro ⟨m, hm⟩
    rw [eB_pow, eB_eq_iff] at hm
    obtain ⟨h1, h2⟩ := hm
    push_cast at h1 h2
    exact zmod7_case_three _ _ _ hi hj h1.symm h2.symm
  · by_cases hj : (j : ZMod 7) = 0
    · refine ⟨sw, sw_mem_normalizer, ?_⟩
      rw [sw_conj_eB, Subgroup.mem_zpowers_iff]
      rintro ⟨m, hm⟩
      rw [eB_pow, eB_eq_iff] at hm
      obtain ⟨h1, h2⟩ := hm
      push_cast at h1 h2
      exact zmod7_case_two _ _ _ hi hj h1.symm h2.symm
    · refine ⟨x1, x1_mem_normalizer, ?_⟩
      rw [x1_conj_eB, Subgroup.mem_zpowers_iff]
      rintro ⟨m, hm⟩
      rw [eB_pow, eB_eq_iff] at hm
      obtain ⟨h1, h2⟩ := hm
      push_cast at h1 h2
      exact zmod7_case_one _ _ _ hi hj h1.symm h2.symm

end B0

end CFSG.RankThree.PartOne.TAIL
