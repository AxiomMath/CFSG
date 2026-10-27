module

public import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType.FF81.RootFusionLin

theorem exists_injective_hom_of_centralizer_equiv {G Γ A B : Type*} [Group G] [Group Γ]
    [Group A] [Group B] (Y : Subgroup G) (φ : ↥Y ≃* Γ) (t g : G) (htY : t ∈ Y)
    (hC : Subgroup.centralizer ({t} : Set G) ≤ Y) (hx : g * t * g⁻¹ ∈ Y)
    (eA : A ≃* Subgroup.centralizer ({φ ⟨g * t * g⁻¹, hx⟩} : Set Γ))
    (eB : B ≃* Subgroup.centralizer ({φ ⟨t, htY⟩} : Set Γ)) :
    ∃ ψ : A →* B, Function.Injective ψ := by
  classical
  set x' : ↥Y := ⟨g * t * g⁻¹, hx⟩ with hx'
  set t' : ↥Y := ⟨t, htY⟩ with ht'
  let w : Subgroup.centralizer ({φ x'} : Set Γ) → G := fun z => ((φ.symm z.1 : ↥Y) : G)
  have hw_mul : ∀ z₁ z₂, w (z₁ * z₂) = w z₁ * w z₂ := by
    intro z₁ z₂
    simp [w]
  have hw_one : w 1 = 1 := by simp [w]
  have hw_comm : ∀ z, w z * (g * t * g⁻¹) = (g * t * g⁻¹) * w z := by
    intro z
    have h := Subgroup.mem_centralizer_singleton_iff.mp z.2
    have h2 : φ.symm z.1 * x' = x' * φ.symm z.1 := by
      have := congrArg φ.symm h
      simpa using this
    exact congrArg Subtype.val h2
  have hw_cent : ∀ z, g⁻¹ * w z * g ∈ Subgroup.centralizer ({t} : Set G) := by
    intro z
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g⁻¹ * w z * g * t = g⁻¹ * (w z * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * w z) * g := by rw [hw_comm z]
      _ = t * (g⁻¹ * w z * g) := by group
  have hw_Y : ∀ z, g⁻¹ * w z * g ∈ Y := fun z => hC (hw_cent z)
  have hf_mem : ∀ z, φ ⟨g⁻¹ * w z * g, hw_Y z⟩ ∈ Subgroup.centralizer ({φ t'} : Set Γ) := by
    intro z
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have h := hw_cent z
    rw [Subgroup.mem_centralizer_singleton_iff] at h
    simpa [ht'] using h
  let f : Subgroup.centralizer ({φ x'} : Set Γ) →* Subgroup.centralizer ({φ t'} : Set Γ) :=
    { toFun := fun z => ⟨φ ⟨g⁻¹ * w z * g, hw_Y z⟩, hf_mem z⟩
      map_one' := by
        apply Subtype.ext
        have : (⟨g⁻¹ * w 1 * g, hw_Y 1⟩ : ↥Y) = 1 := by
          apply Subtype.ext
          simp [hw_one]
        simp [this]
      map_mul' := by
        intro z₁ z₂
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        rw [← map_mul]
        congr 1
        apply Subtype.ext
        simp only [Subgroup.coe_mul, hw_mul]
        group }
  have hf : Function.Injective f := by
    intro z₁ z₂ h
    have h1 : φ ⟨g⁻¹ * w z₁ * g, hw_Y z₁⟩ = φ ⟨g⁻¹ * w z₂ * g, hw_Y z₂⟩ :=
      congrArg Subtype.val h
    have h2 := φ.injective h1
    have h3 : g⁻¹ * w z₁ * g = g⁻¹ * w z₂ * g := congrArg Subtype.val h2
    have h4 : w z₁ = w z₂ := mul_left_cancel (mul_right_cancel h3)
    have h5 : φ.symm z₁.1 = φ.symm z₂.1 := Subtype.ext h4
    exact Subtype.ext (φ.symm.injective h5)
  exact ⟨eB.symm.toMonoidHom.comp (f.comp eA.toMonoidHom),
    eB.symm.injective.comp (hf.comp eA.injective)⟩

end CFSG.StandardType.FF81.RootFusionLin

end
