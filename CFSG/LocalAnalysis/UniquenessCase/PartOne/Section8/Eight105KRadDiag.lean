module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KRadSetup
import CFSG.LocalAnalysis.StandardType.GGSecFiveJRootCoreOmEigen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105

open Matrix
open CFSG.Assembly.LowTwoRank (StatedSU)

variable {K : Type} [Field K]

private theorem eigSU_eq_map_of_conj_diagonal {n q : ℕ} {y : StatedSU n q K}
    {P : GL (Fin n) K} {d : Fin n → K}
    (hy : ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (P : Matrix (Fin n) (Fin n) K) * diagonal d *
        ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (μ : K) :
    eigSU y μ = (Module.End.eigenspace (Matrix.toLin' (diagonal d)) μ).map
      (LinearMap.GeneralLinearGroup.toLinearEquiv (Matrix.GeneralLinearGroup.toLin P) :
        (Fin n → K) →ₗ[K] (Fin n → K)) := by
  have he_apply (v : Fin n → K) :
      ((LinearMap.GeneralLinearGroup.toLinearEquiv (Matrix.GeneralLinearGroup.toLin P) :
        (Fin n → K) →ₗ[K] (Fin n → K))) v = (P : Matrix (Fin n) (Fin n) K) *ᵥ v := rfl
  have hPP : (P : Matrix (Fin n) (Fin n) K) *
      ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hP'P : ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (P : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hprod : ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((P : Matrix (Fin n) (Fin n) K) * diagonal d *
        ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
      diagonal d * ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hP'P, Matrix.one_mul]
  have hProd : ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (P : Matrix (Fin n) (Fin n) K) =
      (P : Matrix (Fin n) (Fin n) K) * diagonal d := by
    rw [hy, Matrix.mul_assoc, hP'P, Matrix.mul_one]
  ext v
  rw [mem_eigSU, Submodule.mem_map]
  constructor
  · intro hv
    refine ⟨((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v, ?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
      have hv' := congrArg
        (fun u => ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u) hv
      rw [hy, mulVec_smul, mulVec_mulVec, hprod, ← mulVec_mulVec] at hv'
      exact hv'
    · rw [he_apply, mulVec_mulVec, hPP, Matrix.one_mulVec]
  · rintro ⟨w, hw, rfl⟩
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hw
    rw [he_apply]
    calc ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
          ((P : Matrix (Fin n) (Fin n) K) *ᵥ w)
        = (((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            (P : Matrix (Fin n) (Fin n) K)) *ᵥ w := by rw [mulVec_mulVec]
      _ = ((P : Matrix (Fin n) (Fin n) K) * diagonal d) *ᵥ w := by rw [hProd]
      _ = (P : Matrix (Fin n) (Fin n) K) *ᵥ (diagonal d *ᵥ w) := by rw [← mulVec_mulVec]
      _ = (P : Matrix (Fin n) (Fin n) K) *ᵥ (μ • w) := by rw [hw]
      _ = μ • ((P : Matrix (Fin n) (Fin n) K) *ᵥ w) := by rw [mulVec_smul]

theorem finrank_eigSU_of_conj_diagonal {n q : ℕ} {y : StatedSU n q K} {P : GL (Fin n) K}
    {d : Fin n → K}
    (hy : ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (P : Matrix (Fin n) (Fin n) K) * diagonal d *
        ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (μ : K) : Module.finrank K (eigSU y μ) = Nat.card {i : Fin n // d i = μ} := by
  classical
  have hP'P : ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (P : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hD : ((P⁻¹ * (y : GL (Fin n) K) * P : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      diagonal d := by
    rw [Units.val_mul, Units.val_mul, hy, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hP'P,
      Matrix.one_mul, Matrix.mul_assoc, hP'P, Matrix.mul_one]
  let x : (Fin n → K) ≃ₗ[K] (Fin n → K) := LinearMap.GeneralLinearGroup.toLinearEquiv
    (Matrix.GeneralLinearGroup.toLin (P⁻¹ * (y : GL (Fin n) K) * P))
  have hx (v : Fin n → K) : x v = diagonal d *ᵥ v := congrArg (fun M => M *ᵥ v) hD
  rw [eigSU_eq_map_of_conj_diagonal hy μ, LinearEquiv.finrank_map_eq]
  exact CFSG.StandardType.jcoreOm_finrank_eigen (x := x)
    (fun v c => by rw [hx, mulVec_diagonal]) μ
    (fun v => by rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, hx])

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105
