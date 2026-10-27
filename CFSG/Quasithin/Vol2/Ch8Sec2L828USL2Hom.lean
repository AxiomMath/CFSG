module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828USL2Card
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.Quasithin.H13

section SLHom

variable {F M K : Type} [Field F] [AddCommGroup M] [Module F M] [Group K]

@[expose] noncomputable def ob5mat (b : Module.Basis (Fin 2) F M) (x : (M →ₗ[F] M)ˣ) :
    Matrix (Fin 2) (Fin 2) F :=
  LinearMap.toMatrixAlgEquiv b (x : M →ₗ[F] M)

theorem ob5_sl_hom [Group.IsPerfect K] (b : Module.Basis (Fin 2) F M) (φ : K →* (M →ₗ[F] M)ˣ) :
    ∃ θ : K →* Matrix.SpecialLinearGroup (Fin 2) F,
      ∀ κ : K, ((θ κ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        ob5mat b (φ κ) := by
  let δ : K →* Fˣ := (Units.map (LinearMap.det : (M →ₗ[F] M) →* F)).comp φ
  have hδ : ∀ κ : K, δ κ = 1 := by
    intro κ
    have hker := Abelianization.commutator_subset_ker δ
    have htop : (commutator K : Subgroup K) = ⊤ := by
      rw [← Group.IsPerfect.commutator_eq_top]
    have hκ : κ ∈ (commutator K : Subgroup K) := by
      rw [htop]
      exact Subgroup.mem_top κ
    exact (MonoidHom.mem_ker.mp (hker hκ))
  have hdet : ∀ κ : K, (ob5mat b (φ κ)).det = 1 := by
    intro κ
    have h1 : (ob5mat b (φ κ)).det = LinearMap.det ((φ κ : (M →ₗ[F] M)ˣ) : M →ₗ[F] M) := by
      unfold ob5mat
      rw [← LinearMap.det_toMatrix b]
      rfl
    rw [h1]
    have h2 := hδ κ
    simp only [δ, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe] at h2
    have h3 : ((LinearMap.det : (M →ₗ[F] M) →* F) ((φ κ : (M →ₗ[F] M)ˣ) : M →ₗ[F] M)) = 1 := by
      have := congrArg Units.val h2
      simpa using this
    simpa using h3
  refine ⟨{ toFun := fun κ => ⟨ob5mat b (φ κ), hdet κ⟩
            map_one' := ?_
            map_mul' := ?_ }, fun κ => rfl⟩
  · apply Subtype.ext
    simp [ob5mat]
  · intro κ κ'
    apply Subtype.ext
    simp only [ob5mat, map_mul, Units.val_mul, Subgroup.coe_mul]
    rfl

end SLHom

end CFSG.Quasithin.H13
