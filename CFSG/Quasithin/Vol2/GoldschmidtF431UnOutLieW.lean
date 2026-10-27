module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutLieBar

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.EvenBN.U4 CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin
open scoped commutatorElement

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) [CharP K 2]

theorem wcl_factor_of_mem_Ssd {B : Subgroup (Xg h)} {hB : FStab h B} {F : Subgroup (K ≃+* K)}
    {α : MulAut (Xg h)} (hα : α ∈ Ssd h B hB F) :
    ∃ s ∈ B, ∃ φ ∈ F, α = cj h s * fa h φ ∧ miyamotoFieldFactor h α = φ := by
  obtain ⟨s, hs, φ, hφ, rfl⟩ := hα
  exact ⟨s, hs, φ, hφ, rfl, miyamotoFieldFactor_conj_mul h s φ⟩

theorem wcl_cj_of_mem_Ssd_bot {B : Subgroup (Xg h)} {hB : FStab h B} {α : MulAut (Xg h)}
    (hα : α ∈ Ssd h B hB ⊥) : ∃ s ∈ B, α = cj h s := by
  obtain ⟨s, hs, φ, hφ, rfl⟩ := hα
  rw [Subgroup.mem_bot] at hφ
  subst hφ
  exact ⟨s, hs, by rw [fa_one, mul_one]⟩

theorem wcl_mem_Ssd_bot_of_factor {B : Subgroup (Xg h)} {hB : FStab h B}
    {F : Subgroup (K ≃+* K)} {α : MulAut (Xg h)} (hα : α ∈ Ssd h B hB F)
    (h1 : miyamotoFieldFactor h α = 1) : α ∈ Ssd h B hB ⊥ := by
  obtain ⟨s, hs, φ, -, rfl, hφ⟩ := wcl_factor_of_mem_Ssd h hα
  rw [h1] at hφ
  subst hφ
  exact ⟨s, hs, 1, Subgroup.one_mem _, rfl⟩

theorem wcl_commutator_le (B : Subgroup (Xg h)) (hB : FStab h B) (F : Subgroup (K ≃+* K)) :
    ⁅Ssd h B hB F, Ssd h B hB F⁆ ≤ Ssd h B hB ⊥ := by
  rw [Subgroup.commutator_le]
  intro α hα β hβ
  have hc : ⁅α, β⁆ ∈ Ssd h B hB F := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hα hβ) (inv_mem hα)) (inv_mem hβ)
  refine wcl_mem_Ssd_bot_of_factor h hc ?_
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact aut_comm h _ _

theorem wcl_Pfx_le : Pfx h ≤ Psy h := fun _ hx => hx.1

theorem W_le (F₂ : Subgroup (K ≃+* K)) :
    spWf (Ssd h (Psy h) (fStab_Psy h) F₂) (fbar h) ≤ Ssd h (Psy h) (fStab_Psy h) ⊥ := by
  intro x hx
  have hx' : x ∈ ⁅spTf (Ssd h (Psy h) (fStab_Psy h) F₂) (fbar h),
      spTf (Ssd h (Psy h) (fStab_Psy h) F₂) (fbar h)⁆ := hx.2
  rw [spTf_Ssd] at hx'
  exact Ssd_mono h (wcl_Pfx_le h) le_rfl (wcl_commutator_le h _ _ _ hx')

end CFSG.Quasithin.H13.F431.Un.OL
