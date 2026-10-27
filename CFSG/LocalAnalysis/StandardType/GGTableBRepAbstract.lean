module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TWFrobAux

public section

namespace CFSG.StandardType

private theorem mulAut_mul_conj_mul_inv {R : Type} [Group R] (f : MulAut R) (g : R) :
    f * MulAut.conj g * f⁻¹ = MulAut.conj (f g) := by
  ext x
  simp only [MulAut.mul_apply, MulAut.inv_apply, MulAut.conj_apply]
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

private theorem mulAut_conj_mul {R : Type} [Group R] (t : MulAut R) (y : R) :
    t * MulAut.conj y = MulAut.conj (t y) * t := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply]
  rw [map_mul, map_mul, map_inv]

theorem ggTableB_representative_of_conj_fixed {R : Type} [Group R] {I : Set (MulAut R)}
    (hinn : ∀ ρ : R, MulAut.conj ρ ∈ I) (f : MulAut R) (S : Set (MulAut R)) (c : MulAut R)
    (hc : c ∈ (MulAut.conj : R →* MulAut R).range)
    (hfix : ∀ s ∈ S, f * (c * s * c⁻¹) = c * s * c⁻¹ * f) :
    ∃ u ∈ I, ∀ s ∈ S, Commute (u * f) s := by
  rcases hc with ⟨g, rfl⟩
  have hc_inv : (MulAut.conj g)⁻¹ = MulAut.conj g⁻¹ :=
    (map_inv (MulAut.conj : R →* MulAut R) g).symm
  refine ⟨(MulAut.conj g)⁻¹ * f * MulAut.conj g * f⁻¹, ?_, ?_⟩
  · have hmem : (MulAut.conj g)⁻¹ * f * MulAut.conj g * f⁻¹ = MulAut.conj (g⁻¹ * f g) := by
      rw [hc_inv]
      rw [show MulAut.conj g⁻¹ * f * MulAut.conj g * f⁻¹
            = MulAut.conj g⁻¹ * (f * MulAut.conj g * f⁻¹) by group]
      rw [mulAut_mul_conj_mul_inv]
      rw [← map_mul]
    rw [hmem]
    exact hinn (g⁻¹ * f g)
  · intro s hs
    have huf : ((MulAut.conj g)⁻¹ * f * MulAut.conj g * f⁻¹) * f
        = (MulAut.conj g)⁻¹ * f * MulAut.conj g := by group
    rw [huf]
    have hcomm : ((MulAut.conj g)⁻¹ * f * MulAut.conj g) * s
        = s * ((MulAut.conj g)⁻¹ * f * MulAut.conj g) := by
      calc
        ((MulAut.conj g)⁻¹ * f * MulAut.conj g) * s
            = (MulAut.conj g)⁻¹ * (f * (MulAut.conj g * s * (MulAut.conj g)⁻¹)) * MulAut.conj g := by
                group
        _ = (MulAut.conj g)⁻¹ * ((MulAut.conj g * s * (MulAut.conj g)⁻¹) * f) * MulAut.conj g := by
                rw [hfix s hs]
        _ = s * ((MulAut.conj g)⁻¹ * f * MulAut.conj g) := by group
    exact hcomm

theorem ggTableB_absorption_of_conj_diag {R : Type} [Group R] {I : Set (MulAut R)}
    (D : Subgroup (MulAut R)) (hD : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x)
    (hI : ∀ i ∈ I, ∃ ρ : R, ∃ δ ∈ D, i = MulAut.conj ρ * δ)
    (S : Set (MulAut R)) (c : MulAut R) (hc : c ∈ (MulAut.conj : R →* MulAut R).range)
    (hS : ∀ s ∈ S, c * s * c⁻¹ ∈ D) :
    ∀ i ∈ I, ∃ ρ : R, ∃ t : MulAut R, i = MulAut.conj ρ * t ∧ ∀ s ∈ S, Commute t s := by
  intro i hi
  obtain ⟨ρ₀, δ, hδmem, hi⟩ := hI i hi
  rcases hc with ⟨g, rfl⟩
  let t : MulAut R := (MulAut.conj g)⁻¹ * δ * MulAut.conj g
  have ht : t = (MulAut.conj g)⁻¹ * δ * MulAut.conj g := rfl
  have hc_inv : (MulAut.conj g)⁻¹ = MulAut.conj g⁻¹ :=
    (map_inv (MulAut.conj : R →* MulAut R) g).symm
  refine ⟨ρ₀ * g * t g⁻¹, t, ?_, ?_⟩
  · rw [hi]
    have hδ_eq : δ = MulAut.conj g * t * (MulAut.conj g)⁻¹ := by
      rw [ht]; group
    rw [hδ_eq]
    rw [show MulAut.conj (ρ₀ * g * t g⁻¹)
          = MulAut.conj ρ₀ * MulAut.conj g * MulAut.conj (t g⁻¹) by
        rw [map_mul, map_mul]]
    have hkey : MulAut.conj g * t * (MulAut.conj g)⁻¹
        = MulAut.conj g * MulAut.conj (t g⁻¹) * t := by
      rw [hc_inv]
      rw [show MulAut.conj g * t * MulAut.conj g⁻¹
            = MulAut.conj g * (t * MulAut.conj g⁻¹) by group]
      rw [mulAut_conj_mul]
      group
    rw [hkey]
    group
  · intro s hs
    rw [ht]
    have hδcomm : δ * (MulAut.conj g * s * (MulAut.conj g)⁻¹)
        = (MulAut.conj g * s * (MulAut.conj g)⁻¹) * δ :=
      hD δ hδmem (MulAut.conj g * s * (MulAut.conj g)⁻¹) (hS s hs)
    have hcomm : ((MulAut.conj g)⁻¹ * δ * MulAut.conj g) * s
        = s * ((MulAut.conj g)⁻¹ * δ * MulAut.conj g) := by
      calc
        ((MulAut.conj g)⁻¹ * δ * MulAut.conj g) * s
            = (MulAut.conj g)⁻¹ * (δ * (MulAut.conj g * s * (MulAut.conj g)⁻¹)) * MulAut.conj g := by
                group
        _ = (MulAut.conj g)⁻¹ * ((MulAut.conj g * s * (MulAut.conj g)⁻¹) * δ) * MulAut.conj g := by
                rw [hδcomm]
        _ = s * ((MulAut.conj g)⁻¹ * δ * MulAut.conj g) := by group
    exact hcomm

end CFSG.StandardType
