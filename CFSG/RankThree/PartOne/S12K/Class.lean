module

public import CFSG.RankThree.PartOne.S12K.OutOfLayer
import CFSG.RankThree.PartOne.S10.AmbientTheta

public section

namespace CFSG.RankThree.PartOne.S12K

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.GroupTheory
open CFSG.RankThree.PartOne.OutStructure

theorem kf1215Class_holds : KF1215Class := by
  intro G _ _ p A c L E ctx b K I X P Q hL hC hF n hn hnI
  have h := ctx.hyp
  have hp := h.prime
  have hp5 : 5 ≤ p := by
    have h3 := h.three_lt
    rcases Nat.lt_or_ge p 5 with h5 | h5
    · obtain rfl : p = 4 := by omega
      exact absurd hp (by norm_num)
    · exact h5
  have hperf : Group.IsPerfect ↥I := isPerfect_of_mem_thetaComponentsAt hL.I_mem
  obtain ⟨r, hr1, hr12, hrow, -⟩ := ctx.facts.three.2
  have hOut : OutPNice p (↥I ⧸ Subgroup.center ↥I) :=
    outPNice_of_layerModel hp hp5 hF.model ⟨r, hr1, hr12, hrow⟩
  obtain ⟨hcN, hc1, hcp, -⟩ := hF.field
  have := h.A_elem
  have hcpow : c ^ p = 1 :=
    CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) c h.c_mem
  have hnc : n * c * n⁻¹ ∈ Subgroup.zpowers c := by
    unfold cNormalizer at hn
    exact (Subgroup.mem_normalizer_iff.1 hn c).1 (Subgroup.mem_zpowers c)
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hnc
  have hdvd : (p : ℤ) ∣ m - 1 := by
    refine normalizer_power_of_outPNice hp I hOut hcN hnI ?_ hc1 (m := m) ?_
    · rw [hcpow]
      exact one_mem _
    · rw [← hm, ← zpow_add, add_neg_cancel, zpow_zero]
      exact one_mem _
  have hord : (orderOf c : ℤ) ∣ m - 1 :=
    (Int.natCast_dvd_natCast.2 (orderOf_dvd_of_pow_eq_one hcpow)).trans hdvd
  have h1 : c ^ (m - 1) = 1 := orderOf_dvd_iff_zpow_eq_one.1 hord
  rw [← hm]
  have : c ^ m = c ^ (m - 1) * c := by rw [← zpow_add_one]; congr 1; ring
  rw [this, h1, one_mul]

end CFSG.RankThree.PartOne.S12K
