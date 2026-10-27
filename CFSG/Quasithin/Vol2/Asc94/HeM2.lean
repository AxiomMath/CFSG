module

public import CFSG.Quasithin.Vol2.Asc94.HeM1

public section

namespace CFSG.Quasithin.A94.L52

open Matrix CFSG.CGT.M24S

private theorem conj_A2_mem_A1 {x y : Hc} (hx : x ∈ A1) (hy : y ∈ A2) : y * x * y⁻¹ ∈ A1 := by
  have hc := (comm_coord hx hy).1
  have e : y * x * y⁻¹ = (x * y * x⁻¹ * y⁻¹)⁻¹ * x := by group
  rw [e]
  exact A1.mul_mem (A1.inv_mem (Subgroup.mem_inf.1 hc).1) hx

theorem A2_le_normalizer_A1 : A2 ≤ Subgroup.normalizer (A1 : Set Hc) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => conj_A2_mem_A1 (show x ∈ A1 from hx) hy, fun hx => ?_⟩
  have hx' : y * x * y⁻¹ ∈ A1 := hx
  have h := conj_A2_mem_A1 hx' (A2.inv_mem hy)
  have e : y⁻¹ * (y * x * y⁻¹) * y⁻¹⁻¹ = x := by group
  rw [e] at h
  exact h

theorem card_Jm : Nat.card Jm = 2 ^ 8 := by
  haveI := Subgroup.normal_subgroupOf_of_le_normalizer A2_le_normalizer_A1
  haveI := Subgroup.normal_subgroupOf_sup_of_le_normalizer A2_le_normalizer_A1
  have hiso : A1.relIndex A2 = A1.relIndex (A2 ⊔ A1) :=
    Nat.card_congr
      (QuotientGroup.quotientInfEquivProdNormalizerQuotient A2 A1 A2_le_normalizer_A1).toEquiv
  have h2 : A1.relIndex A2 * Nat.card ↥(A1 ⊓ A2) = Nat.card ↥A2 :=
    Subgroup.relIndex_mul_card A1 A2
  have h3 : A1.relIndex (A2 ⊔ A1) * Nat.card ↥(A1 ⊓ (A2 ⊔ A1)) = Nat.card ↥(A2 ⊔ A1) :=
    Subgroup.relIndex_mul_card A1 (A2 ⊔ A1)
  have e4 : (2 : ℕ) ^ 4 = 16 := by norm_num
  have e6 : (2 : ℕ) ^ 6 = 64 := by norm_num
  have e8 : (2 : ℕ) ^ 8 = 256 := by norm_num
  rw [card_A1_inf_A2, card_A2, e4, e6] at h2
  rw [inf_eq_left.2 (le_sup_right : A1 ≤ A2 ⊔ A1), card_A1, e6] at h3
  rw [Jm, sup_comm, e8]
  omega

theorem zC_zt : zC zt = Matrix.of ![![0, 1], ![0, 0]] := by
  ext i j
  rw [zC_apply, cm_zt]
  fin_cases i <;> fin_cases j <;> decide

theorem det_zC_zt : (zC zt).det = 0 := by
  rw [zC_zt, Matrix.det_fin_two_of]
  simp

end CFSG.Quasithin.A94.L52
