module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitOrthA
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaTypeAAux

public section

namespace CFSG.StandardType

theorem ggCoxFork_absurd_typeA {ι : Type} {M : CoxeterMatrix ι} {m : ℕ} {σ : Fin m ≃ ι}
    (hM : M = (CoxeterMatrix.A m).reindex σ) {t₀ t₁ t₂ t₃ : M.Group}
    (h₀ : ∃ (w : M.Group) (i : ι), t₀ = w * M.simple i * w⁻¹)
    (h₁ : ∃ (w : M.Group) (i : ι), t₁ = w * M.simple i * w⁻¹)
    (h₂ : ∃ (w : M.Group) (i : ι), t₂ = w * M.simple i * w⁻¹)
    (h₃ : ∃ (w : M.Group) (i : ι), t₃ = w * M.simple i * w⁻¹)
    (h12 : t₁ * t₂ = t₂ * t₁) (h13 : t₁ * t₃ = t₃ * t₁) (h23 : t₂ * t₃ = t₃ * t₂)
    (hn12 : t₁ ≠ t₂) (hn13 : t₁ ≠ t₃) (hn23 : t₂ ≠ t₃)
    (hn01 : t₀ * t₁ ≠ t₁ * t₀) (hn02 : t₀ * t₂ ≠ t₂ * t₀) (hn03 : t₀ * t₃ ≠ t₃ * t₀) :
    False := by
  subst hM
  obtain ⟨φ, hφ⟩ := ggOrthA_reindex_groupEquiv_A σ
  have hrefl : ∀ x : ((CoxeterMatrix.A m).reindex σ).Group,
      (∃ w i, x = w * ((CoxeterMatrix.A m).reindex σ).simple i * w⁻¹) →
        ∃ γ, ggOrthA_AReflRoot m (φ x) γ := by
    rintro x ⟨w, i, rfl⟩
    exact Exists.intro _ (Exists.intro (φ w) (Exists.intro (σ.symm i)
      (And.intro (by rw [map_mul, map_mul, map_inv, hφ]) rfl)))
  obtain ⟨γ₀, hγ₀⟩ := hrefl t₀ h₀
  obtain ⟨γ₁, hγ₁⟩ := hrefl t₁ h₁
  obtain ⟨γ₂, hγ₂⟩ := hrefl t₂ h₂
  obtain ⟨γ₃, hγ₃⟩ := hrefl t₃ h₃
  have h12' : φ t₁ * φ t₂ = φ t₂ * φ t₁ := by rw [← map_mul, ← map_mul, h12]
  have h13' : φ t₁ * φ t₃ = φ t₃ * φ t₁ := by rw [← map_mul, ← map_mul, h13]
  have h23' : φ t₂ * φ t₃ = φ t₃ * φ t₂ := by rw [← map_mul, ← map_mul, h23]
  have hn12' : φ t₁ ≠ φ t₂ := fun h => hn12 (φ.injective h)
  have hn13' : φ t₁ ≠ φ t₃ := fun h => hn13 (φ.injective h)
  have hn23' : φ t₂ ≠ φ t₃ := fun h => hn23 (φ.injective h)
  have hn01' : φ t₀ * φ t₁ ≠ φ t₁ * φ t₀ := by
    intro h
    exact hn01 (φ.injective (by simpa only [← map_mul] using h))
  have hn02' : φ t₀ * φ t₂ ≠ φ t₂ * φ t₀ := by
    intro h
    exact hn02 (φ.injective (by simpa only [← map_mul] using h))
  have hn03' : φ t₀ * φ t₃ ≠ φ t₃ * φ t₀ := by
    intro h
    exact hn03 (φ.injective (by simpa only [← map_mul] using h))
  exact ggNEA_fork_absurd_WA hγ₀ hγ₁ hγ₂ hγ₃ h12' h13' h23' hn12' hn13' hn23'
    hn01' hn02' hn03'

end CFSG.StandardType

end
