module

public import CFSG.GroupTheory.QuasiDihedralFusion.SemidihedralClassification

public section

namespace CFSG.Sporadic.Recognition.JankoWong

section SD16

open CFSG.Open CFSG.Semidihedral

private theorem rs_sq_four : (r 4 * s 4) ^ 2 = z 4 := by
  simpa only [pow_one] using reflection_square_nat 4 (by norm_num) 1

private theorem sdV_sq_four : (r 4 ^ (2 ^ (4 - 3))) ^ 2 = z 4 := by
  rw [← pow_mul, z, half_eq_two_mul_quarter (by norm_num), mul_comm]

end SD16

open CFSG.QuasiDihedralFusion
open CFSG.Semidihedral (r s)

theorem exists_dihedral_kernel_of_semidihedral_selfcentralizing
    {K : Type} [Group K] [Finite K] (S : Sylow 2 K)
    (hS : Nonempty (CFSG.Open.SemidihedralGroup 4 ≃* ↥S))
    {z : K} (hzS : z ∈ S) (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1)
    (hzc : ∀ y ∈ S, y * z = z * y)
    (hC : ∀ g : K, g * z = z * g → g ∈ S)
    (hNC : ¬ CFSG.HasNormalPComplement 2 K) :
    ∃ L : Subgroup K, L.Normal ∧ L.index = 2 ∧ (∀ M : Subgroup L, M.index ≠ 2) ∧
      CFSG.GorensteinWalter.HasDihedralSylowTwo L ∧ z ∈ L ∧
      (∀ u : K, u ^ 2 = 1 → u ≠ 1 → IsConj u z) := by
  obtain ⟨f⟩ := hS
  have hz_mem : z ∈ centerOf (S : Subgroup K) :=
    Subgroup.mem_inf.mpr ⟨hzS, Subgroup.mem_centralizer_iff.mpr hzc⟩
  rw [centerOf_eq_zpowers_z (by norm_num) (S : Subgroup K) f] at hz_mem
  set ι := CFSG.Semidihedral.FocalFusion.ambientHom 4 (S : Subgroup K) f
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz_mem
  have hw2 : ι (CFSG.Semidihedral.z 4) ^ 2 = 1 := by
    rw [← map_pow, CFSG.Semidihedral.z_sq 4 (by norm_num), map_one]
  have hzι : z = ι (CFSG.Semidihedral.z 4) := by
    obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
    · exact absurd (by rw [← hk, zpow_mul]; simp [hw2]) hz1
    · rw [← hk, zpow_add, zpow_mul]
      simp [hw2]
  have hnb : ¬ IsConj (ι (r 4 * s 4)) (ι (r 4 ^ (2 ^ (4 - 3)))) := by
    intro hb
    obtain ⟨c, hc⟩ := isConj_iff.mp hb
    have hcz : c * z * c⁻¹ = z := by
      calc c * z * c⁻¹ = c * ι (r 4 * s 4) ^ 2 * c⁻¹ := by rw [hzι, ← map_pow, rs_sq_four]
        _ = (c * ι (r 4 * s 4) * c⁻¹) ^ 2 := conj_pow.symm
        _ = ι (r 4 ^ (2 ^ (4 - 3))) ^ 2 := by rw [hc]
        _ = z := by rw [hzι, ← map_pow, sdV_sq_four]
    have hcS : c ∈ (S : Subgroup K) := hC c (mul_inv_eq_iff_eq_mul.mp hcz)
    have hvmem : ι (r 4 ^ (2 ^ (4 - 3))) ∈ (CFSG.Semidihedral.rotationSubgroup 4).map ι :=
      ⟨_, sdV_mem_rotationSubgroup 4, rfl⟩
    have h1 := conj_mem_map_ambientHom (S : Subgroup K) f _
      (CFSG.Semidihedral.rotationSubgroup_normal 4 (by norm_num)) c⁻¹
      ((S : Subgroup K).inv_mem hcS) _ hvmem
    have h2 : c⁻¹ * ι (r 4 ^ (2 ^ (4 - 3))) * c⁻¹⁻¹ = ι (r 4 * s 4) := by
      rw [← hc]
      group
    rw [h2, ambientHom_mem_map_iff] at h1
    exact rs_not_mem_rotationSubgroup (by norm_num) h1
  by_cases ha : IsConj (ι (s 4)) (ι (CFSG.Semidihedral.z 4))
  · obtain ⟨⟨L, hLn, hL2, hLM, hLD⟩, -, -, -, -⟩ :=
      semidihedralFusionD_of (by norm_num) S f ha hnb
    refine ⟨L, hLn, hL2, hLM, hLD, ?_, ?_⟩
    · rw [hzι, ← sdV_sq_four, map_pow]
      exact Subgroup.sq_mem_of_index_two hL2 _
    · intro u hu2 hu1
      have hall : ∀ x : K, orderOf x = 2 → IsConj x (ι (CFSG.Semidihedral.z 4)) := fun x hx => by
        rcases involution_isConj_cases (by norm_num) S f x hx with h | h
        · exact h.symm
        · exact h.symm.trans ha
      exact (hall u (orderOf_eq_prime hu2 hu1)).trans (hall z (orderOf_eq_prime hz2 hz1)).symm
  · exact absurd (semidihedralFusionComplement_of (by norm_num) S f ha hnb).normalComplement hNC

end CFSG.Sporadic.Recognition.JankoWong
