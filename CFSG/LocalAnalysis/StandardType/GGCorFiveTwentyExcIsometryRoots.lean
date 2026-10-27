module

public import CFSG.LieType.Chevalley.LangWeylInvolutionReflections

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint RootSpace

variable {τ : Tag}

theorem inner_realExtend_realExtend {θ : Module.End ℤ (Fin τ.rank → ℤ)}
    (hθ : ∀ x y, iform (θ x) (θ y) = iform x y) (x y : RootSpace τ) :
    inner ℝ (realExtend θ x) (realExtend θ y) = inner ℝ x y := by
  obtain ⟨c, _hc, hinner⟩ := exists_inner_ofLattice_eq_iform τ
  have h : (innerₗ (RootSpace τ)).compl₁₂ (realExtend θ) (realExtend θ) =
      innerₗ (RootSpace τ) := by
    refine LinearMap.BilinForm.ext_basis (basis τ) fun k l => ?_
    rw [LinearMap.compl₁₂_apply, innerₗ_apply_apply, innerₗ_apply_apply, basis_apply, basis_apply,
      realExtend_ofLattice, realExtend_ofLattice, hinner, hinner,
      hθ (Pi.single k 1) (Pi.single l 1)]
  have := congrArg (fun B : LinearMap.BilinForm ℝ (RootSpace τ) => B x y) h
  simpa only [LinearMap.compl₁₂_apply, innerₗ_apply_apply] using this

theorem injective_of_iform_isometry {θ : Module.End ℤ (Fin τ.rank → ℤ)}
    (hθ : ∀ x y, iform (θ x) (θ y) = iform x y) : Function.Injective θ := by
  intro x y hxy
  by_contra hne
  have hne' : x - y ≠ 0 := sub_ne_zero.mpr hne
  have hpos : 0 < iform (x - y) (x - y) := iform_self_pos hne'
  have hzero : iform (x - y) (x - y) = 0 := by
    rw [← hθ (x - y) (x - y), map_sub, hxy, sub_self]
    simp [iform]
  exact hpos.ne' hzero

theorem exists_isRoot_eq_of_iform_isometry {θ : Module.End ℤ (Fin τ.rank → ℤ)}
    (hθ : ∀ x y, iform (θ x) (θ y) = iform x y)
    (hΦ : ∀ α, IsRoot τ α → IsRoot τ (θ α)) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    ∃ γ, IsRoot τ γ ∧ θ γ = α := by
  classical
  have hinj : Function.Injective θ := injective_of_iform_isometry hθ
  have hsub : (rootFinset τ).image θ ⊆ rootFinset τ := by
    intro β hβ
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hβ
    exact mem_rootFinset.mpr (hΦ γ (mem_rootFinset.mp hγ))
  have hcard : ((rootFinset τ).image θ).card = (rootFinset τ).card :=
    Finset.card_image_of_injective _ hinj
  have heq : (rootFinset τ).image θ = rootFinset τ :=
    Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)
  have hαmem : α ∈ rootFinset τ := mem_rootFinset.mpr hα
  rw [← heq] at hαmem
  obtain ⟨γ, hγ, hθγ⟩ := Finset.mem_image.mp hαmem
  exact ⟨γ, mem_rootFinset.mp hγ, hθγ⟩

end CFSG.StandardType

end
