module

public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofGL3
public import CFSG.RankThree.PartTwo.KFacts.K71IdentSU3
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering418

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartTwo.KFacts
open Matrix

section OTU

variable {f : ℕ} {F : Type} [Field F]

theorem pow_three_eq_one_of_mem_unitaryScalars (h : UnitaryFieldData 2 f F)
    {z : unitarySU 2 f F 3} (hz : z ∈ unitaryScalars h 3) : z ^ 3 = 1 := by
  obtain ⟨c, -, hc3, hzc⟩ := hz
  apply Subtype.ext
  rw [Subgroup.coe_pow, hzc, ← map_pow, hc3, map_one, Subgroup.coe_one]

theorem eq_one_of_conj_fixed_psu3 (h : UnitaryFieldData 2 f F) (hq : 2 < 2 ^ f)
    {y u : unitaryPSU h 3} (hy3 : (MulAut.conj y : MulAut (unitaryPSU h 3)) ^ 3 = 1)
    (hyu : y * u * y⁻¹ = u) (hu4 : u ^ 4 = 1) (hu2 : u ^ 2 ≠ 1) : y = 1 := by
  have : CharP F 2 := h.charP
  have hy3' : y ^ 3 = 1 := by
    have h1 : y ^ 3 ∈ Subgroup.center (unitaryPSU h 3) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h2 := congrArg (fun f : MulAut (unitaryPSU h 3) => f g) hy3
      simp only [← map_pow, MulAut.conj_apply, MulAut.one_apply] at h2
      exact (mul_inv_eq_iff_eq_mul.mp h2).symm
    rw [center_unitaryPSU_three_eq_bot h hq] at h1
    exact h1
  obtain ⟨A, rfl⟩ := unitaryProj_surjective h 3 y
  obtain ⟨B, rfl⟩ := unitaryProj_surjective h 3 u
  have hA3 : A ^ 3 ∈ unitaryScalars h 3 := by
    rw [← ker_unitaryProj, MonoidHom.mem_ker, map_pow]
    exact hy3'
  have hB4 : B ^ 4 ∈ unitaryScalars h 3 := by
    rw [← ker_unitaryProj, MonoidHom.mem_ker, map_pow]
    exact hu4
  have hB2 : B ^ 2 ∉ unitaryScalars h 3 := by
    intro h2
    apply hu2
    rw [← map_pow]
    exact (MonoidHom.mem_ker.mp ((ker_unitaryProj h 3).symm ▸ h2))
  obtain ⟨z, hz, hABz⟩ : ∃ z ∈ unitaryScalars h 3, A * B * A⁻¹ = B * z := by
    have h2 : unitaryProj h 3 (A * B * A⁻¹) = unitaryProj h 3 B := by
      rw [map_mul, map_mul, map_inv]
      exact hyu
    have h3 : (A * B * A⁻¹)⁻¹ * B ∈ unitaryScalars h 3 := QuotientGroup.eq.mp h2
    refine ⟨((A * B * A⁻¹)⁻¹ * B)⁻¹, inv_mem h3, ?_⟩
    group
  have hzc : Commute B z := (Subgroup.mem_center_iff.mp (unitaryScalars_le_center h 3 hz) B)
  have hAB3 : A * B ^ 3 = B ^ 3 * A := by
    have h1 : A * B ^ 3 * A⁻¹ = (A * B * A⁻¹) ^ 3 := by
      rw [conj_pow]
    rw [hABz, hzc.mul_pow, pow_three_eq_one_of_mem_unitaryScalars h hz, mul_one] at h1
    calc A * B ^ 3 = A * B ^ 3 * A⁻¹ * A := by group
      _ = B ^ 3 * A := by rw [h1]
  have hB12 : (B ^ 3) ^ 4 = 1 := by
    rw [← pow_mul, show 3 * 4 = 4 * 3 by norm_num, pow_mul]
    exact pow_three_eq_one_of_mem_unitaryScalars h hB4
  have hB6 : (B ^ 3) ^ 2 ≠ 1 := by
    intro h2
    apply hB2
    have h6 : B ^ 6 = 1 := by rw [← pow_mul] at h2; exact h2
    have h7 : B ^ 2 = (B ^ 4)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_add]
      exact h6
    rw [h7]
    exact inv_mem hB4
  have hAGL : ((A : GL (Fin 3) F)) ^ 3 ∈ Subgroup.center (GL (Fin 3) F) := by
    obtain ⟨c, -, -, hAc⟩ := hA3
    rw [← Subgroup.coe_pow, hAc, Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  have hcomm : (A : GL (Fin 3) F) * ((B ^ 3 : unitarySU 2 f F 3) : GL (Fin 3) F) =
      ((B ^ 3 : unitarySU 2 f F 3) : GL (Fin 3) F) * (A : GL (Fin 3) F) := by
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hAB3]
  have h4 : ((B ^ 3 : unitarySU 2 f F 3) : GL (Fin 3) F) ^ 4 = 1 := by
    rw [← Subgroup.coe_pow, hB12, Subgroup.coe_one]
  have h2 : ((B ^ 3 : unitarySU 2 f F 3) : GL (Fin 3) F) ^ 2 ≠ 1 := by
    intro h2
    apply hB6
    apply Subtype.ext
    rw [Subgroup.coe_pow, h2, Subgroup.coe_one]
  have hAc := Item8KFacts2Proof.mem_center_of_commute hAGL hcomm h4 h2
  have hAcen : A ∈ Subgroup.center (unitarySU 2 f F 3) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := (Subgroup.mem_center_iff.mp hAc) (g : GL (Fin 3) F)
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact this
  rw [center_unitarySU_three (h := h) hq] at hAcen
  exact (MonoidHom.mem_ker.mp ((ker_unitaryProj h 3).symm ▸ hAcen))

end OTU

end CFSG.RankThree.PartTwo.Sec8.Hering418
