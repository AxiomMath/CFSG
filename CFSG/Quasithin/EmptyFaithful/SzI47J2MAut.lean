module

public import CFSG.Quasithin.SteinbergCBAlternatingAut
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.AutAlternatingFour

public section

namespace CFSG.Quasithin.SzI47J2M

open Equiv

@[expose] def KleinSelfCentralizing (n : ℕ) : Prop :=
  ∀ v₁ : Perm (Fin n), v₁ * v₁ = 1 → v₁ ≠ 1 →
    ∀ v₂ : Perm (Fin n), v₂ * v₂ = 1 → v₂ ≠ 1 → v₁ ≠ v₂ → v₁ * v₂ = v₂ * v₁ →
    ∀ σ : Perm (Fin n), σ * v₁ = v₁ * σ → σ * v₂ = v₂ * σ →
      σ = 1 ∨ σ = v₁ ∨ σ = v₂ ∨ σ = v₁ * v₂

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 1000000 in
theorem kleinSelfCentralizing_four : KleinSelfCentralizing 4 := by
  unfold KleinSelfCentralizing
  decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 1000000 in
theorem kleinSelfCentralizing_five : KleinSelfCentralizing 5 := by
  unfold KleinSelfCentralizing
  decide +kernel

theorem exists_inner_of_fixes_alt {n : ℕ} (hcen : KleinSelfCentralizing n)
    (hsurj : Function.Surjective
      (MulAut.conjNormal : Perm (Fin n) →* MulAut (alternatingGroup (Fin n))))
    {v₁ v₂ : alternatingGroup (Fin n)} (h₁ : v₁ * v₁ = 1) (h₂ : v₂ * v₂ = 1) (h₁' : v₁ ≠ 1)
    (h₂' : v₂ ≠ 1) (h₁₂ : v₁ ≠ v₂) (hc : v₁ * v₂ = v₂ * v₁)
    (α : MulAut (alternatingGroup (Fin n))) (hα₁ : α v₁ = v₁) (hα₂ : α v₂ = v₂) :
    ∃ u : alternatingGroup (Fin n), (u = 1 ∨ u = v₁ ∨ u = v₂ ∨ u = v₁ * v₂) ∧
      ∀ y, α y = u * y * u⁻¹ := by
  obtain ⟨σ, rfl⟩ := hsurj α
  have hcomm : ∀ v : alternatingGroup (Fin n), MulAut.conjNormal σ v = v →
      σ * (v : Perm (Fin n)) = v * σ := fun v hv => by
    have h := congrArg Subtype.val hv
    rw [MulAut.conjNormal_apply] at h
    calc σ * (v : Perm (Fin n)) = σ * v * σ⁻¹ * σ := by group
      _ = v * σ := by rw [h]
  have key := hcen v₁ (congrArg Subtype.val h₁) (fun h => h₁' (Subtype.ext h)) v₂
    (congrArg Subtype.val h₂) (fun h => h₂' (Subtype.ext h)) (fun h => h₁₂ (Subtype.ext h))
    (congrArg Subtype.val hc) σ (hcomm v₁ hα₁) (hcomm v₂ hα₂)
  have conj_eq : ∀ u : alternatingGroup (Fin n), (u : Perm (Fin n)) = σ →
      ∀ y, MulAut.conjNormal σ y = u * y * u⁻¹ := fun u hu y => by
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, ← hu]
    rfl
  rcases key with hσ | hσ | hσ | hσ
  · exact ⟨1, Or.inl rfl, conj_eq 1 hσ.symm⟩
  · exact ⟨v₁, Or.inr (Or.inl rfl), conj_eq v₁ hσ.symm⟩
  · exact ⟨v₂, Or.inr (Or.inr (Or.inl rfl)), conj_eq v₂ hσ.symm⟩
  · exact ⟨v₁ * v₂, Or.inr (Or.inr (Or.inr rfl)), conj_eq (v₁ * v₂) hσ.symm⟩

theorem exists_inner_of_fixes_equiv {Y : Type*} [Group Y] {n : ℕ} (hcen : KleinSelfCentralizing n)
    (hsurj : Function.Surjective
      (MulAut.conjNormal : Perm (Fin n) →* MulAut (alternatingGroup (Fin n))))
    (e : Y ≃* alternatingGroup (Fin n)) {v₁ v₂ : Y} (h₁ : v₁ * v₁ = 1) (h₂ : v₂ * v₂ = 1)
    (h₁' : v₁ ≠ 1) (h₂' : v₂ ≠ 1) (h₁₂ : v₁ ≠ v₂) (hc : v₁ * v₂ = v₂ * v₁) (α : MulAut Y)
    (hα₁ : α v₁ = v₁) (hα₂ : α v₂ = v₂) :
    ∃ u : Y, (u = 1 ∨ u = v₁ ∨ u = v₂ ∨ u = v₁ * v₂) ∧ ∀ y, α y = u * y * u⁻¹ := by
  obtain ⟨u', hu', hα'⟩ := exists_inner_of_fixes_alt hcen hsurj (v₁ := e v₁) (v₂ := e v₂)
    (by rw [← map_mul, h₁, map_one]) (by rw [← map_mul, h₂, map_one])
    (fun h => h₁' (e.injective (h.trans (map_one e).symm)))
    (fun h => h₂' (e.injective (h.trans (map_one e).symm)))
    (fun h => h₁₂ (e.injective h)) (by rw [← map_mul, ← map_mul, hc])
    (e.symm.trans (α.trans e)) (by simp [hα₁]) (by simp [hα₂])
  refine ⟨e.symm u', ?_, fun y => ?_⟩
  · rcases hu' with rfl | rfl | rfl | rfl
    · exact Or.inl (map_one _)
    · exact Or.inr (Or.inl (e.symm_apply_apply _))
    · exact Or.inr (Or.inr (Or.inl (e.symm_apply_apply _)))
    · exact Or.inr (Or.inr (Or.inr (by rw [map_mul, e.symm_apply_apply, e.symm_apply_apply])))
  · apply e.injective
    have h := hα' (e y)
    simpa using h

theorem exists_inner_of_fixes_klein {Y : Type*} [Group Y]
    (hY : Nonempty (Y ≃* alternatingGroup (Fin 4)) ∨ Nonempty (Y ≃* alternatingGroup (Fin 5)))
    {v₁ v₂ : Y} (h₁ : v₁ * v₁ = 1) (h₂ : v₂ * v₂ = 1) (h₁' : v₁ ≠ 1) (h₂' : v₂ ≠ 1)
    (h₁₂ : v₁ ≠ v₂) (hc : v₁ * v₂ = v₂ * v₁) (α : MulAut Y) (hα₁ : α v₁ = v₁)
    (hα₂ : α v₂ = v₂) :
    ∃ u : Y, (u = 1 ∨ u = v₁ ∨ u = v₂ ∨ u = v₁ * v₂) ∧ ∀ y, α y = u * y * u⁻¹ := by
  rcases hY with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact exists_inner_of_fixes_equiv kleinSelfCentralizing_four
      (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_four_bijective_conj.2) e h₁ h₂ h₁'
      h₂' h₁₂ hc α hα₁ hα₂
  · exact exists_inner_of_fixes_equiv kleinSelfCentralizing_five
      (CFSG.Quasithin.SteinbergCB.conjPerm_surjective (n := 5) (Or.inl rfl)) e h₁ h₂ h₁' h₂' h₁₂
      hc α hα₁ hα₂

end CFSG.Quasithin.SzI47J2M
