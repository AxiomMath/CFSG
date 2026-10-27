module

public import CFSG.Yardstones.Mf4cdcdf2e013.Definitions
public import CFSG.LocalAnalysis.PreuniquenessRankFour.BinaryRank

open CFSG.Open

public section

namespace CFSG.Yardstones.Mf4cdcdf2e013

theorem Standing4.two_pow_eight_dvd_card {G : Type} [Group G] [Finite G] (hS : Standing4 G) :
    2 ^ 8 ∣ Nat.card G := by
  obtain ⟨p, hp⟩ := CFSG.PreuniquenessRankFour.Helpers.betaFour_nonempty hS.rank
  have hpp : p.Prime := hp.1
  have hp2 : p ≠ 2 := hp.2.1
  have h4 : 4 ≤ CFSG.Open.uniqueFourTwoLocalRank p G := hp.2.2.2
  obtain ⟨H, hH, hHr⟩ := CFSG.PreuniquenessRankFour.Helpers.twoLocalRank_attained (G := G) p hpp
    (by change 0 < CFSG.Open.uniqueFourTwoLocalRank p G; omega)
  have hrank : 4 ≤ CFSG.Open.pRank p H := by
    change CFSG.Open.pRank p H = CFSG.Open.uniqueFourTwoLocalRank p G at hHr
    omega
  have h256 := CFSG.PreuniquenessRankFour.Helpers.rank_four_local_twoCore_cardinality_at_least_256
    p hpp hp2 hS.charTwo H hH hrank
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.PreuniquenessRankFour.Helpers.pCoreOf_isPGroup 2 H)
  have hk8 : 8 ≤ k := by
    by_contra hlt
    have : 2 ^ k ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hk] at h256
    omega
  exact (pow_dvd_pow 2 hk8).trans (hk ▸ Subgroup.card_subgroup_dvd_card _)

end CFSG.Yardstones.Mf4cdcdf2e013
