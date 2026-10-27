module

public import CFSG.Quasithin.EmptyFaithful.SBc17SL2Defs
public import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Sylow
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

namespace CFSG.Quasithin

namespace SBc17

section Basic

variable {F : Type} [Field F]

private theorem coe_uElt (x : F) : (uElt x : Matrix (Fin 2) (Fin 2) F) = !![1, x; 0, 1] := rfl

private theorem coe_tElt (a : Fˣ) :
    (tElt a : Matrix (Fin 2) (Fin 2) F) = !![(a : F), 0; 0, ((a⁻¹ : Fˣ) : F)] := rfl

private theorem det_entries (g : SL2 F) : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have h := g.2
  rwa [Matrix.det_fin_two] at h

private theorem uElt_injective : Function.Injective (uElt : F → SL2 F) := by
  intro s t h
  have h' := congrArg (fun x : SL2 F => (x : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simpa [coe_uElt] using h'

private theorem eq_one_of_sq_eq_one [CharP F 2] {x : F} (h : x ^ 2 = 1) : x = 1 := by
  have h2 : (x + 1) ^ 2 = 0 := by
    rw [CharTwo.add_sq, h, one_pow, CharTwo.add_self_eq_zero]
  have h3 : x + 1 = 0 := (pow_eq_zero_iff two_ne_zero).1 h2
  rw [← sub_eq_zero, CharTwo.sub_eq_add]
  exact h3

private theorem conj_uElt_entry10 (g : SL2 F) (s : F) :
    ((g * uElt s * g⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) 1 0 = -(s * (g 1 0) ^ 2) := by
  simp [coe_uElt, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

private theorem conj_uElt_of_mem_borelSub {g : SL2 F} (hg : g ∈ borelSub F) (s : F) :
    g * uElt s * g⁻¹ = uElt ((g 0 0) ^ 2 * s) := by
  have h10 : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hg
  have hdet := det_entries g
  rw [h10, mul_zero, sub_zero] at hdet
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;>
    simp [coe_uElt, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two, h10]
  all_goals first | exact hdet | ring1 | linear_combination hdet

theorem normalizer_upperSub_le_borelSub :
    Subgroup.normalizer (upperSub F : Set (SL2 F)) ≤ borelSub F := by
  intro g hg
  rw [Subgroup.mem_set_normalizer_iff] at hg
  obtain ⟨t, ht⟩ := mem_upperSub_iff.1 ((hg (uElt 1)).1 (mem_upperSub_iff.2 ⟨1, rfl⟩))
  have h10 := congrArg (fun x : SL2 F => (x : Matrix (Fin 2) (Fin 2) F) 1 0) ht
  simp only [conj_uElt_entry10, coe_uElt] at h10
  show (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  simpa using h10

theorem borelSub_le_normalizer_upperSub :
    borelSub F ≤ Subgroup.normalizer (upperSub F : Set (SL2 F)) := by
  intro g hg
  rw [Subgroup.mem_set_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨s, rfl⟩ := mem_upperSub_iff.1 hh
    exact mem_upperSub_iff.2 ⟨_, conj_uElt_of_mem_borelSub hg s⟩
  · intro hh
    obtain ⟨s, hs⟩ := mem_upperSub_iff.1 hh
    refine mem_upperSub_iff.2 ⟨((g⁻¹ : SL2 F) 0 0) ^ 2 * s, ?_⟩
    rw [← conj_uElt_of_mem_borelSub (inv_mem hg) s, ← hs]
    group

theorem normalizer_upperSub :
    Subgroup.normalizer (upperSub F : Set (SL2 F)) = borelSub F :=
  le_antisymm normalizer_upperSub_le_borelSub borelSub_le_normalizer_upperSub

end Basic

section FiniteField

open scoped Pointwise

variable {F : Type} [Field F] [Fintype F]

theorem card_upperSub : Nat.card (upperSub F) = Fintype.card F := by
  have e : F ≃ upperSub F := Equiv.ofBijective
    (fun t : F => (⟨uElt t, mem_upperSub_iff.2 ⟨t, rfl⟩⟩ : upperSub F))
    ⟨fun s t h => uElt_injective (congrArg Subtype.val h), fun ⟨_, hg⟩ => by
      obtain ⟨t, rfl⟩ := mem_upperSub_iff.1 hg
      exact ⟨t, rfl⟩⟩
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card]

private theorem card_SL2 : Nat.card (SL2 F) = Fintype.card F * (Fintype.card F ^ 2 - 1) := by
  have h := Matrix.card_SL_mul_card_units (n := Fin 2) (R := F)
  rw [Matrix.card_GL_field, Nat.card_units, Nat.card_eq_fintype_card (α := F)] at h
  simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one] at h
  have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have hq1 : 0 < Fintype.card F - 1 := by omega
  apply Nat.eq_of_mul_eq_mul_right hq1
  rw [h, show Fintype.card F ^ 2 - Fintype.card F = Fintype.card F * (Fintype.card F - 1) by
    rw [Nat.mul_sub_one, sq]]
  ring

theorem isSylow_upperSub [CharP F 2] (_hq : 4 ≤ Fintype.card F) :
    IsPGroup 2 (upperSub F) ∧ ¬ 2 ∣ (upperSub F).index := by
  obtain ⟨⟨n, hn0⟩, -, hn⟩ := FiniteField.card F 2
  simp only [PNat.mk_coe] at hn
  have hcard : Nat.card (upperSub F) = 2 ^ n := by rw [card_upperSub, hn]
  refine ⟨IsPGroup.of_card hcard, ?_⟩
  have h := (upperSub F).index_mul_card
  rw [hcard, card_SL2, hn] at h
  have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
  have hidx : (upperSub F).index = (2 ^ n) ^ 2 - 1 :=
    Nat.eq_of_mul_eq_mul_right hpos (by rw [h, mul_comm])
  rw [hidx, ← pow_mul]
  have h2 : 2 ∣ 2 ^ (n * 2) := dvd_pow_self 2 (by omega)
  have h1 : 1 ≤ 2 ^ (n * 2) := Nat.one_le_two_pow
  generalize 2 ^ (n * 2) = x at h1 h2
  omega

theorem exists_conj_upperSub [CharP F 2] (hq : 4 ≤ Fintype.card F) {P : Subgroup (SL2 F)}
    (hP : IsPGroup 2 P) (hidx : ¬ 2 ∣ P.index) :
    ∃ g : SL2 F, ∀ x : SL2 F, x ∈ P ↔ g⁻¹ * x * g ∈ upperSub F := by
  obtain ⟨hU, hUidx⟩ := isSylow_upperSub (F := F) hq
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SL2 F) (hU.toSylow hUidx) (hP.toSylow hidx)
  refine ⟨g, fun x => ?_⟩
  have hP' : (MulAut.conj g • upperSub F : Subgroup (SL2 F)) = P :=
    congrArg (fun S : Sylow 2 (SL2 F) => (S : Subgroup (SL2 F))) hg
  rw [← hP', Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  show (MulAut.conj g)⁻¹ x ∈ upperSub F ↔ _
  rw [MulAut.conj_inv_apply]

theorem le_upperSub_of_normalized_two [CharP F 2] (hq : 4 ≤ Fintype.card F)
    {W : Subgroup (SL2 F)} (hW2 : IsPGroup 2 W)
    (hWn : upperSub F ≤ Subgroup.normalizer (W : Set (SL2 F))) : W ≤ upperSub F := by
  obtain ⟨hU, hUidx⟩ := isSylow_upperSub (F := F) hq
  have hsup : IsPGroup 2 (W ⊔ upperSub F : Subgroup (SL2 F)) := hW2.to_sup_of_normal_left' hU hWn
  have hmax : W ⊔ upperSub F = upperSub F := (hU.toSylow hUidx).is_maximal' hsup le_sup_right
  exact hmax ▸ le_sup_left

theorem center_borelSub [CharP F 2] (hq : 4 ≤ Fintype.card F) :
    ∀ z ∈ borelSub F, (∀ b ∈ borelSub F, z * b = b * z) → z = 1 := by
  intro z hz hcomm
  have hnt : Nontrivial Fˣ := by
    rw [← Finite.one_lt_card_iff_nontrivial, Nat.card_units, Nat.card_eq_fintype_card]
    omega
  obtain ⟨a, ha⟩ := exists_ne (1 : Fˣ)
  have hz10 : (z : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hz
  have hdet := det_entries z
  rw [hz10, mul_zero, sub_zero] at hdet
  have h1 := hcomm (tElt a) (torusSub_le_borelSub ⟨by simp [coe_tElt], by simp [coe_tElt]⟩)
  have h1' := congrArg (fun x : SL2 F => (x : Matrix (Fin 2) (Fin 2) F) 0 1) h1
  simp [coe_tElt, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] at h1'
  have hβ : (z : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
    have h2 : (z : Matrix (Fin 2) (Fin 2) F) 0 1 * ((a : F)⁻¹ - (a : F)) = 0 := by
      linear_combination h1'
    rcases mul_eq_zero.1 h2 with h | h
    · exact h
    · exfalso
      have h3 : (a : F)⁻¹ = a := sub_eq_zero.1 h
      have h4 : (a : F) ^ 2 = 1 := by
        have := mul_inv_cancel₀ a.ne_zero
        rw [h3] at this
        rwa [sq]
      exact ha (Units.ext (eq_one_of_sq_eq_one h4))
  have h5 := hcomm (uElt 1) (upperSub_le_borelSub (mem_upperSub_iff.2 ⟨1, rfl⟩))
  have h5' := congrArg (fun x : SL2 F => (x : Matrix (Fin 2) (Fin 2) F) 0 1) h5
  simp [coe_uElt, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] at h5'
  have h6 : (z : Matrix (Fin 2) (Fin 2) F) 0 0 = (z : Matrix (Fin 2) (Fin 2) F) 1 1 := by
    linear_combination h5'
  have h7 : (z : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    apply eq_one_of_sq_eq_one
    rw [sq]
    nth_rewrite 2 [h6]
    exact hdet
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp [h7, ← h6, hβ, hz10]

end FiniteField

end SBc17

end CFSG.Quasithin
