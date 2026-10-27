module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherConjDescentFixed

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.LinearGroups
open scoped Pointwise

variable {f : ℕ} {K : Type} [Field K] {n : ℕ} (h : UnitaryFieldData 2 f K)

theorem mulVecLin_conj_hermTransvection_unitarySU (g : unitarySU 2 f K n)
    {x : unitarySU 2 f K n} {a : Fin n → K} {c : K}
    (hx : mulVecLin ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      hermTransvection (stdHermForm h n) a c) :
    mulVecLin (((g * x * g⁻¹ : unitarySU 2 f K n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      hermTransvection (stdHermForm h n) (g • a) c := by
  refine LinearMap.ext fun v => ?_
  have hgi : g • g⁻¹ • v = v := smul_inv_smul g v
  have hiso := stdHermForm_smul_smul h g a (g⁻¹ • v)
  rw [hgi] at hiso
  have hxv := LinearMap.congr_fun hx (g⁻¹ • v)
  rw [mulVecLin_apply] at hxv
  rw [hermTransvection_apply, hiso, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul,
    Units.val_mul, mulVecLin_apply, ← mulVec_mulVec, ← mulVec_mulVec]
  change ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
    (((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (g⁻¹ • v)) = _
  rw [hxv, hermTransvection_apply, mulVec_add, mulVec_smul]
  change g • g⁻¹ • v + _ • (g • a) = _
  rw [hgi]

end CFSG.SeitzReduction.UnitaryPilot
