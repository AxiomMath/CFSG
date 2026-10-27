module

import Lean
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDiagCommonAux2
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {f : ℕ} {ψ : Su K 2 f 6 →* G}

theorem ggNSPosPF3C_lift_mul_scalar_of_pow_three (h : GGNSLocalHyp 3 B Bs K f 6 ψ) {b : G}
    {g : GL (Fin 6) K} (hg : GGInducesUnitary (p := 2) (f := f) ψ b g) (t : Kˣ)
    (h3 : (g * Matrix.GeneralLinearGroup.scalar (Fin 6) t) ^ 3 = 1) :
    GGInducesUnitary (p := 2) (f := f) ψ b (g * Matrix.GeneralLinearGroup.scalar (Fin 6) t) := by
  have hf : 1 ≤ f := ggNSPosPE_one_le_f_aux h.prime h.odd h.dvd
  have hdata := ggNSPosPE_unitaryFieldData_aux h.card hf
  have hcomm : Commute g (Matrix.GeneralLinearGroup.scalar (Fin 6) t) :=
    (Matrix.GeneralLinearGroup.scalar_commute t g).symm
  have h3' : g ^ 3 * (Matrix.GeneralLinearGroup.scalar (Fin 6) t) ^ 3 = 1 := by
    rw [← hcomm.mul_pow]
    exact h3
  have hs3 : (Matrix.GeneralLinearGroup.scalar (Fin 6) t) ^ 3 =
      Matrix.GeneralLinearGroup.scalar (Fin 6) (t ^ 3) := by
    rw [← map_pow]
  have hgp : g ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) ((t ^ 3)⁻¹) := by
    rw [mul_eq_one_iff_eq_inv.mp h3', hs3, map_inv]
  have hu : ((((t ^ 3)⁻¹ : Kˣ) : K)) ^ (2 ^ f + 1) = 1 :=
    ggNSPosPE_norm_one_of_pow_scalar (n := 6) (by norm_num) (u := (t ^ 3)⁻¹) hg.1 hgp
  have hu' : (t : K) ^ (3 * (2 ^ f + 1)) = 1 := by
    have hh := hu
    rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, inv_pow, ← pow_mul] at hh
    exact inv_eq_one.mp hh
  have hr3 : ((t : K) ^ (2 ^ f + 1)) ^ 3 = 1 := by
    rw [← pow_mul, mul_comm (2 ^ f + 1) 3]
    exact hu'
  have hr : (t : K) ^ (2 ^ f + 1) = 1 :=
    TableBUD.eq_one_of_fixed_of_pow hdata h.dvd (TableBUD.norm_pow_fixed hdata (t : K)) hr3
  have hst : ggIsUnitaryMat (p := 2) (f := f) (Matrix.GeneralLinearGroup.scalar (Fin 6) t) :=
    (ggNSPosPE_scalar_isUnitary_iff (f := f) (n := 6) (by norm_num) t).mpr hr
  have hmu : ggIsUnitaryMat (p := 2) (f := f)
      (g * Matrix.GeneralLinearGroup.scalar (Fin 6) t) :=
    ggNSPosPE_isUnitaryMat_mul hg.1 hst
  refine ⟨hmu, ?_⟩
  intro x
  obtain ⟨y, hy, hact⟩ := hg.2 x
  refine ⟨y, ?_, hact⟩
  have hsx : Matrix.GeneralLinearGroup.scalar (Fin 6) t * (x : GL (Fin 6) K) *
      (Matrix.GeneralLinearGroup.scalar (Fin 6) t)⁻¹ = (x : GL (Fin 6) K) := by
    rw [Matrix.GeneralLinearGroup.scalar_commute t (x : GL (Fin 6) K), mul_assoc,
      mul_inv_cancel, mul_one]
  have hconj : (g * Matrix.GeneralLinearGroup.scalar (Fin 6) t) * (x : GL (Fin 6) K) *
      (g * Matrix.GeneralLinearGroup.scalar (Fin 6) t)⁻¹ = g * (x : GL (Fin 6) K) * g⁻¹ := by
    rw [_root_.mul_inv_rev]
    calc (g * Matrix.GeneralLinearGroup.scalar (Fin 6) t) * (x : GL (Fin 6) K) *
          ((Matrix.GeneralLinearGroup.scalar (Fin 6) t)⁻¹ * g⁻¹)
        = g * (Matrix.GeneralLinearGroup.scalar (Fin 6) t * (x : GL (Fin 6) K) *
            (Matrix.GeneralLinearGroup.scalar (Fin 6) t)⁻¹) * g⁻¹ := by group
      _ = g * (x : GL (Fin 6) K) * g⁻¹ := by rw [hsx]
  rw [hconj]
  exact hy

end CFSG.StandardType

end
