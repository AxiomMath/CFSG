module

public import CFSG.Yardstones.Mf4cdcdf2e013.Definitions
import CFSG.RankThree.PartTwo.Census.Criteria
import CFSG.RankThree.OddKernel.ThreeComplementQuotient
import CFSG.LocalAnalysis.PreuniquenessRankFour.Helpers

public section

namespace CFSG.Yardstones.Mf4cdcdf2e013

open CFSG.Open

variable {G H : Type} [Group G] [Finite G] [Group H]

theorem Standing4.false_of_not_isCharTwoType (hS : Standing4 G) (e : G ≃* H)
    (hH : ¬ IsCharTwoType H) : False :=
  hH (CFSG.RankThree.PartTwo.Census.isCharTwoType_of_mulEquiv e hS.charTwo)

theorem Standing4.false_of_localRank_le_three (hS : Standing4 G) (e : G ≃* H)
    (h : ∀ [Finite H] (r : ℕ), r.Prime → r ≠ 2 → CFSG.Assembly.RankThreeEven.localRank r H ≤ 3) :
    False := by
  have : Finite H := Finite.of_equiv G e.toEquiv
  have hle : evenRank G ≤ evenRank H :=
    CFSG.RankThree.PartOne.Census3.evenRank_le_of_mulEquiv e
  have h2 : evenRank H ≤ 3 :=
    CFSG.RankThree.OddKernel.evenRank_le_of_localRank_le fun r hr hr2 => h r hr hr2
  have h4 : 4 ≤ evenRank G := hS.rank
  omega

theorem Standing4.false_of_localRank_le_two (hS : Standing4 G) (e : G ≃* H)
    (h : ∀ [Finite H] (r : ℕ), r.Prime → r ≠ 2 → CFSG.Assembly.RankThreeEven.localRank r H ≤ 2) :
    False :=
  hS.false_of_localRank_le_three e fun r hr hr2 => (h r hr hr2).trans (by norm_num)

theorem Standing4.false_of_pRank_le_two (hS : Standing4 G) (e : G ≃* H)
    (h : ∀ [Finite H] (r : ℕ), r.Prime → r ≠ 2 →
      CFSG.Assembly.pRank r (⊤ : Subgroup H) ≤ 2) : False :=
  hS.false_of_localRank_le_two e fun r hr hr2 =>
    CFSG.RankThree.PartTwo.Census.localRank_le_of_pRank_le hr (h r hr hr2)

theorem Standing4.false_of_card (hS : Standing4 G) (e : G ≃* H) {N : ℕ} (E : Finset ℕ)
    (hN : Nat.card H = N)
    (hE : ∀ [Finite H] (r : ℕ), r ∈ E → r.Prime → r ≠ 2 →
      CFSG.Assembly.RankThreeEven.localRank r H ≤ 2)
    (hcube : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∉ E → ¬ r ^ 3 ∣ N) : False := by
  refine hS.false_of_localRank_le_three e fun r hr hr2 => ?_
  by_cases hrE : r ∈ E
  · exact (hE r hrE hr hr2).trans (by norm_num)
  · have hcube' : ¬ r ^ 3 ∣ Nat.card H := by
      rw [hN]
      exact hcube r hr hr2 hrE
    exact (CFSG.RankThree.PartTwo.Census.localRank_le_of_pRank_le hr
      (CFSG.RankThree.PartTwo.Census.pRank_le_two_of_not_dvd hr hcube')).trans (by norm_num)

theorem three_mem_uniqueFourBeta_of_card (hS : Standing4 G)
    (h4 : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ 3 → ¬ r ^ 4 ∣ Nat.card G) : 3 ∈ uniqueFourBeta G := by
  obtain ⟨p, hp⟩ := CFSG.PreuniquenessRankFour.Helpers.betaFour_nonempty hS.rank
  have hglob : 4 ≤ CFSG.Open.pRank p (⊤ : Subgroup G) :=
    CFSG.PreuniquenessRankFour.Helpers.betaFour_globalRank hp
  have hdvd0 : p ^ CFSG.Open.pRank p (⊤ : Subgroup G) ∣ Nat.card (⊤ : Subgroup G) :=
    CFSG.RankThreeEvenClassification.Helpers.prime_power_pRank_dvd_card p hp.1 ⊤
  rw [Subgroup.card_top] at hdvd0
  have hpow : p ^ 4 ∣ Nat.card G := (pow_dvd_pow p hglob).trans hdvd0
  have hp3 : p = 3 := by
    by_contra hne
    exact h4 p hp.1 hp.2.1 hne hpow
  have hmem : p ∈ uniqueFourBeta G := hp
  rwa [hp3] at hmem

end CFSG.Yardstones.Mf4cdcdf2e013
