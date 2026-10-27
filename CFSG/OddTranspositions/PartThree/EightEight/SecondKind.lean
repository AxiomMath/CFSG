module

public import CFSG.Timmesfeld.Bridge.Asc72Triangle
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore
public import Certificates.Certificate43

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge Asc72

theorem orderOf_mul_eq_four_of_map_eq {G K : Type*} [Group G] [Finite G] [Group K] {D : Set G}
    (hD : CFSG.Timmesfeld.Bridge.Asc72.IsOddTransp D)
    (hN : CFSG.Timmesfeld.Connectivity.IsNormalSet D)
    {u w v : G} (ht : CFSG.Timmesfeld.Bridge.Asc72.IsTriangle D u w v) (φ : G →* K)
    (huv : φ u = φ v) (hodd : Odd (orderOf (φ u * φ w))) (h1 : 1 < orderOf (φ u * φ w)) :
    orderOf (u * v * w) = 4 := by
  have hu2 : φ u * φ u = 1 := by
    rw [← map_mul, hD.mul_self_eq_one ht.1, map_one]
  have hw2 : φ w * φ w = 1 := by
    rw [← map_mul, hD.mul_self_eq_one ht.2.2.1, map_one]
  have hw1 : φ w ≠ 1 := by
    intro hw
    have hdvd : orderOf (φ u * φ w) ∣ 2 := by
      rw [hw, mul_one]
      exact orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hu2)
    obtain ⟨k, hk⟩ := hodd
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hword : orderOf (φ w) = 2 := orderOf_eq_prime (by rwa [pow_two]) hw1
  have hmap : φ (u * v * w) = φ w := by
    rw [map_mul, map_mul, ← huv, hu2, one_mul]
  rcases IsTriangle.orderOf_cases hD hN ht with ⟨hoddord, -⟩ | h4 | ⟨n, hnodd, -, hord⟩
  ·
    exfalso
    have hdvd : 2 ∣ orderOf (u * v * w) := by
      rw [← hword, ← hmap]
      exact orderOf_map_dvd φ (u * v * w)
    exact (Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr hdvd)) hoddord
  ·
    exact h4
  ·
    exfalso
    obtain ⟨-, -, hcu, -, -, -⟩ := IsTriangle.third_kind hD hN ht hnodd hord
    have hwn : (φ w) ^ n = φ w := by
      obtain ⟨k, rfl⟩ := hnodd
      rw [pow_succ, pow_mul, sq, hw2, one_pow, one_mul]
    have hcw : Commute (φ w) (φ u) := by
      have h := hcu.map φ
      simpa [map_pow, hmap, hwn] using h
    have hsq : (φ u * φ w) * (φ u * φ w) = 1 := by
      have h := (commute_iff_mul_sq_eq_one hu2 hw2).mp hcw.symm
      simpa [pow_two] using h
    have hdvd : orderOf (φ u * φ w) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
    obtain ⟨k, hk⟩ := hodd
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    omega

end CFSG.OddTranspositions.PartThree

end
