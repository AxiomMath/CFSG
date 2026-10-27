module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import Mathlib.RepresentationTheory.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.Zass

open scoped MatrixGroups

section PGL

variable {K : Type*} [Field K] {M : Type*} [AddCommGroup M] [Module K M] {G : Type*} [Group G]

@[expose] def restrictHom (ρ : Representation K G M) (W : Submodule K M) (T : Subgroup G)
    (hT : ∀ g ∈ T, ∀ x ∈ W, ρ g x ∈ W) : T →* Module.End K W where
  toFun g := (ρ g).restrict (hT g g.2)
  map_one' := LinearMap.ext fun x => Subtype.ext (by simp)
  map_mul' g h := LinearMap.ext fun x => Subtype.ext (by simp [Module.End.mul_apply])

@[simp] theorem restrictHom_apply_coe (ρ : Representation K G M) (W : Submodule K M)
    (T : Subgroup G) (hT : ∀ g ∈ T, ∀ x ∈ W, ρ g x ∈ W) (g : T) (x : W) :
    ((restrictHom ρ W T hT g x : W) : M) = ρ g x := rfl

theorem exists_hom_pgl (ρ : Representation K G M) (W : Submodule K M)
    (hW : Module.finrank K W = 2) (T : Subgroup G) (hT : ∀ g ∈ T, ∀ x ∈ W, ρ g x ∈ W) :
    ∃ θ : T →* PGL(2, K), ∀ g : T, θ g = 1 ↔ ∃ μ : K, ∀ x ∈ W, ρ g x = μ • x := by
  haveI : Module.Finite K W := Module.finite_of_finrank_pos (by omega)
  let b : Module.Basis (Fin 2) K W := Module.finBasisOfFinrankEq K W hW
  let ψ : Module.End K W →* Matrix (Fin 2) (Fin 2) K :=
    (LinearMap.toMatrixAlgEquiv b : Module.End K W ≃ₐ[K] Matrix (Fin 2) (Fin 2) K)
  let θ₀ : T →* GL (Fin 2) K := (ψ.comp (restrictHom ρ W T hT)).toHomUnits
  refine ⟨Matrix.ProjGenLinGroup.mk.comp θ₀, fun g => ?_⟩
  rw [MonoidHom.comp_apply, Matrix.ProjGenLinGroup.mk_eq_one,
    Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
  have hval : ((θ₀ g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      LinearMap.toMatrixAlgEquiv b (restrictHom ρ W T hT g) := rfl
  rw [hval]
  constructor
  · rintro ⟨μ, hμ⟩
    refine ⟨μ, fun x hx => ?_⟩
    have h1 : LinearMap.toMatrixAlgEquiv b (restrictHom ρ W T hT g) =
        LinearMap.toMatrixAlgEquiv b (algebraMap K (Module.End K W) μ) := by
      rw [AlgEquiv.commutes, ← hμ]
      simp [Matrix.scalar_apply, Matrix.algebraMap_eq_diagonal]
    have h2 := congrArg (fun f : Module.End K W => (f ⟨x, hx⟩ : M))
      ((LinearMap.toMatrixAlgEquiv b).injective h1)
    simpa using h2
  · rintro ⟨μ, hμ⟩
    refine ⟨μ, ?_⟩
    have h1 : restrictHom ρ W T hT g = algebraMap K (Module.End K W) μ :=
      LinearMap.ext fun x => Subtype.ext (by simpa using hμ x x.2)
    rw [h1, AlgEquiv.commutes]
    simp [Matrix.algebraMap_eq_diagonal]

end PGL

end CFSG.LocalAnalysis.UniquenessCase.UCK.Zass
