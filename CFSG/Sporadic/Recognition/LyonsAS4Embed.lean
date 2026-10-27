module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Equiv Equiv.Perm Subgroup

@[expose] def shift3 : Fin 8 ↪ Fin 11 :=
  ⟨fun i => ⟨i.val + 3, by omega⟩, fun i j h => Fin.ext (by simpa using congrArg Fin.val h)⟩

theorem shift3_val (i : Fin 8) : (shift3 i).val = i.val + 3 :=
  rfl

theorem mem_range_shift3 {j : Fin 11} : j ∈ Set.range shift3 ↔ 3 ≤ j.val := by
  constructor
  · rintro ⟨i, rfl⟩
    rw [shift3_val]
    omega
  · intro hj
    exact ⟨⟨j.val - 3, by omega⟩, Fin.ext (by rw [shift3_val]; show j.val - 3 + 3 = j.val; omega)⟩

@[expose] def fix012 : Subgroup (Perm (Fin 11)) where
  carrier := {σ | σ 0 = 0 ∧ σ 1 = 1 ∧ σ 2 = 2}
  mul_mem' := by
    rintro σ τ ⟨h0, h1, h2⟩ ⟨h0', h1', h2'⟩
    exact ⟨by simp [h0, h0'], by simp [h1, h1'], by simp [h2, h2']⟩
  one_mem' := ⟨rfl, rfl, rfl⟩
  inv_mem' := by
    rintro σ ⟨h0, h1, h2⟩
    exact ⟨Perm.inv_eq_iff_eq.2 h0.symm, Perm.inv_eq_iff_eq.2 h1.symm,
      Perm.inv_eq_iff_eq.2 h2.symm⟩

theorem mem_fix012 {τ : Perm (Fin 11)} : τ ∈ fix012 ↔ τ 0 = 0 ∧ τ 1 = 1 ∧ τ 2 = 2 :=
  Iff.rfl

@[expose] noncomputable def embed8 : Perm (Fin 8) →* Perm (Fin 11) :=
  extendDomainHom (ofInjective shift3 shift3.injective)

theorem embed8_injective : Function.Injective embed8 :=
  extendDomainHom_injective _

theorem embed8_shift3 (σ : Perm (Fin 8)) (i : Fin 8) : embed8 σ (shift3 i) = shift3 (σ i) :=
  extendDomain_apply_image σ (ofInjective shift3 shift3.injective) i

theorem embed8_apply (σ : Perm (Fin 8)) (i : Fin 8) :
    embed8 σ ⟨i.val + 3, by omega⟩ = ⟨(σ i).val + 3, by omega⟩ :=
  embed8_shift3 σ i

theorem embed8_apply_of_lt (σ : Perm (Fin 8)) (j : Fin 11) (hj : j.val < 3) : embed8 σ j = j :=
  extendDomain_apply_not_subtype σ (ofInjective shift3 shift3.injective)
    (fun h => by have := mem_range_shift3.1 h; omega)

theorem embed8_mem_fix012 (σ : Perm (Fin 8)) : embed8 σ ∈ fix012 :=
  ⟨embed8_apply_of_lt σ 0 (by decide), embed8_apply_of_lt σ 1 (by decide),
    embed8_apply_of_lt σ 2 (by decide)⟩

theorem sign_embed8 (σ : Perm (Fin 8)) : sign (embed8 σ) = sign σ :=
  sign_extendDomain σ (ofInjective shift3 shift3.injective)

theorem cycleType_embed8 (σ : Perm (Fin 8)) : (embed8 σ).cycleType = σ.cycleType :=
  cycleType_extendDomain (ofInjective shift3 shift3.injective)

theorem embed8_mem_alternatingGroup_iff (σ : Perm (Fin 8)) :
    embed8 σ ∈ alternatingGroup (Fin 11) ↔ σ ∈ alternatingGroup (Fin 8) := by
  simp [mem_alternatingGroup, sign_embed8]

theorem fix012_apply_of_lt {τ : Perm (Fin 11)} (h : τ ∈ fix012) {j : Fin 11} (hj : j.val < 3) :
    τ j = j := by
  have key : ∀ j : Fin 11, j.val < 3 → j = 0 ∨ j = 1 ∨ j = 2 := by decide
  obtain ⟨h0, h1, h2⟩ := h
  rcases key j hj with rfl | rfl | rfl <;> assumption

theorem three_le_apply_of_mem_fix012 {τ : Perm (Fin 11)} (h : τ ∈ fix012) {j : Fin 11}
    (hj : 3 ≤ j.val) : 3 ≤ (τ j).val := by
  by_contra hlt
  have h1 : τ (τ j) = τ j := fix012_apply_of_lt h (by omega)
  have h2 : τ j = j := τ.injective h1
  rw [h2] at hlt
  omega

theorem exists_embed8_eq {τ : Perm (Fin 11)} (h : τ ∈ fix012) :
    ∃ σ : Perm (Fin 8), embed8 σ = τ := by
  have hdown : ∀ j : Fin 11, 3 ≤ j.val → shift3 ⟨j.val - 3, by omega⟩ = j := fun j hj =>
    Fin.ext (by rw [shift3_val]; show j.val - 3 + 3 = j.val; omega)
  have hτ : ∀ i : Fin 8, 3 ≤ (τ (shift3 i)).val := fun i =>
    three_le_apply_of_mem_fix012 h (by rw [shift3_val]; omega)
  have hτ' : ∀ i : Fin 8, 3 ≤ (τ⁻¹ (shift3 i)).val := fun i =>
    three_le_apply_of_mem_fix012 (inv_mem h) (by rw [shift3_val]; omega)
  let σ : Perm (Fin 8) :=
    { toFun := fun i => ⟨(τ (shift3 i)).val - 3, by omega⟩
      invFun := fun i => ⟨(τ⁻¹ (shift3 i)).val - 3, by omega⟩
      left_inv := fun i => by
        apply Fin.ext
        show (τ⁻¹ (shift3 ⟨(τ (shift3 i)).val - 3, _⟩)).val - 3 = i.val
        rw [hdown _ (hτ i), show τ⁻¹ (τ (shift3 i)) = shift3 i from τ.symm_apply_apply _,
          shift3_val]
        omega
      right_inv := fun i => by
        apply Fin.ext
        show (τ (shift3 ⟨(τ⁻¹ (shift3 i)).val - 3, _⟩)).val - 3 = i.val
        rw [hdown _ (hτ' i), show τ (τ⁻¹ (shift3 i)) = shift3 i from τ.apply_symm_apply _,
          shift3_val]
        omega }
  refine ⟨σ, Perm.ext fun j => ?_⟩
  by_cases hj : j.val < 3
  · rw [embed8_apply_of_lt σ j hj, fix012_apply_of_lt h hj]
  · obtain ⟨i, rfl⟩ := mem_range_shift3.2 (not_lt.1 hj)
    rw [embed8_shift3]
    exact hdown _ (hτ i)

theorem existsUnique_embed8_eq {τ : Perm (Fin 11)} (h : τ ∈ fix012) :
    ∃! σ : Perm (Fin 8), embed8 σ = τ := by
  obtain ⟨σ, hσ⟩ := exists_embed8_eq h
  exact ⟨σ, hσ, fun σ' hσ' => embed8_injective (hσ'.trans hσ.symm)⟩

theorem range_embed8 : embed8.range = fix012 := by
  ext τ
  constructor
  · rintro ⟨σ, rfl⟩
    exact embed8_mem_fix012 σ
  · exact exists_embed8_eq

theorem map_embed8_alternatingGroup :
    (alternatingGroup (Fin 8)).map embed8 = fix012 ⊓ alternatingGroup (Fin 11) := by
  ext τ
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨embed8_mem_fix012 σ, (embed8_mem_alternatingGroup_iff σ).2 hσ⟩
  · rintro ⟨hτ, hτA⟩
    obtain ⟨σ, rfl⟩ := exists_embed8_eq hτ
    exact ⟨σ, (embed8_mem_alternatingGroup_iff σ).1 hτA, rfl⟩

@[expose] noncomputable def fix012Equiv : ↥fix012 ≃* Perm (Fin 8) :=
  ((MonoidHom.ofInjective embed8_injective).trans (MulEquiv.subgroupCongr range_embed8)).symm

theorem embed8_fix012Equiv (τ : ↥fix012) : embed8 (fix012Equiv τ) = (τ : Perm (Fin 11)) := by
  simp [fix012Equiv]

theorem fix012Equiv_symm_apply (σ : Perm (Fin 8)) :
    fix012Equiv.symm σ = ⟨embed8 σ, embed8_mem_fix012 σ⟩ :=
  fix012Equiv.symm_apply_eq.2
    (embed8_injective (embed8_fix012Equiv ⟨embed8 σ, embed8_mem_fix012 σ⟩)).symm

end CFSG.Sporadic.Recognition.LyonsSims
