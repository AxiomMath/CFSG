module

public import CFSG.Quasithin.Background.RonanH46ZQ

public section

namespace CFSG.Quasithin.RonanH46

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3 Matrix
  CFSG.Quasithin.RonanH44
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem hermBlkZ_mul_inv (X Y : HMod 1 K) :
    hermBlkZ (Y * X⁻¹) = hermBlkZ Y - hermBlkZ X := by
  ext i j
  simp [hermBlkZ, mat_mul, mat_inv, sub_eq_add_neg]

theorem QZ_comm_V2z (hK : Nat.card K = (2 ^ 1) ^ 2) :
    ∀ q ∈ (QZs K).map (rho hK), ∀ x ∈ V2z 1 K, q x * x⁻¹ ∈ V1z 1 K := by
  intro q hq x hx
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hq
  have hb : hermBlkZ x = 0 := mem_V2z_iff_hermBlkZ.1 hx
  have b00 : mat x 1 1 = 0 := by simpa [hermBlkZ] using congrFun (congrFun hb 0) 0
  have b10 : mat x 2 1 = 0 := by simpa [hermBlkZ] using congrFun (congrFun hb 1) 0
  have b01 : mat x 1 2 = 0 := by simpa [hermBlkZ] using congrFun (congrFun hb 0) 1
  have b11 : mat x 2 2 = 0 := by simpa [hermBlkZ] using congrFun (congrFun hb 1) 1
  rw [mem_V1z_iff_row]
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_V2z_iff_hermBlkZ, hermBlkZ_mul_inv, QZ_act_block hK hg, sub_self]
  · have r := QZ_act_row hK hg x 0
    simp only [Fin.succ_zero_eq_one] at r
    rw [mat_mul, mat_inv, Matrix.add_apply, Matrix.neg_apply, r, b00, b10]
    ring
  · have r := QZ_act_row hK hg x 1
    simp only [Fin.succ_one_eq_two] at r
    rw [mat_mul, mat_inv, Matrix.add_apply, Matrix.neg_apply, r, b01, b11]
    ring

theorem V2z_char (hK : Nat.card K = (2 ^ 1) ^ 2) :
    ∀ x : HMod 1 K, x ∈ V2z 1 K ↔ ∀ q ∈ (QZs K).map (rho hK), q x * x⁻¹ ∈ V1z 1 K := by
  intro x
  constructor
  · intro hx q hq
    exact QZ_comm_V2z hK q hq x hx
  · intro h
    obtain ⟨g₁, hg₁, g₁01, g₁02⟩ := exists_QZs (1 : K) 0
    obtain ⟨g₂, hg₂, g₂01, g₂02⟩ := exists_QZs (0 : K) 1
    have h1 := mem_V1z_iff_row.1 (h _ (Subgroup.mem_map.2 ⟨g₁, hg₁, rfl⟩))
    have h2 := mem_V1z_iff_row.1 (h _ (Subgroup.mem_map.2 ⟨g₂, hg₂, rfl⟩))
    have a11 : mat x 1 1 = 0 := by
      have e := h1.2.1
      have r := QZ_act_row hK hg₁ x 0
      simp only [Fin.succ_zero_eq_one] at r
      rw [mat_mul, mat_inv, Matrix.add_apply, Matrix.neg_apply, r, g₁01, g₁02] at e
      linear_combination e
    have a12 : mat x 1 2 = 0 := by
      have e := h1.2.2
      have r := QZ_act_row hK hg₁ x 1
      simp only [Fin.succ_one_eq_two] at r
      rw [mat_mul, mat_inv, Matrix.add_apply, Matrix.neg_apply, r, g₁01, g₁02] at e
      linear_combination e
    have a22 : mat x 2 2 = 0 := by
      have e := h2.2.2
      have r := QZ_act_row hK hg₂ x 1
      simp only [Fin.succ_one_eq_two] at r
      rw [mat_mul, mat_inv, Matrix.add_apply, Matrix.neg_apply, r, g₂01, g₂02] at e
      linear_combination e
    exact mem_V2z.2 ⟨a11, a12, a22⟩

end CFSG.Quasithin.RonanH46
