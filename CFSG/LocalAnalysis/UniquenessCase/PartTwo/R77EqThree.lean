module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Conclusion76Three
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07Eq
import CFSG.LocalAnalysis.UniquenessCase.UC6R77RankBound
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SigmaRankThree13
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3A9Rank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedFive StronglyEmbeddedThree)

variable {G : Type} [Group G] [Finite G]

theorem r77Eq_dataOfSetup (hSE : StronglyEmbeddedFive) (hSE3 : StronglyEmbeddedThree)
    (hS : Standing G) (hUC : rankThreeUC G) (S : Setup G) :
    UC22.F07.R77Eq (dataOfSetup hS S) := by
  intro _ p hp hp2 hsp r hr hr2 hrσ X hXM hXp hnc hexp hcl h2 _
  have hpP : p.Prime := ((dataOfSetup hS S).sig_prime p hp).1
  haveI : Fact p.Prime := ⟨hpP⟩
  haveI : Fact r.Prime := ⟨hr⟩
  have hpr : p ≠ r := fun h => hrσ (h ▸ hp)
  have hXr : CFSG.Open.pRank r X ≤ CFSG.Open.pRank r S.M :=
    CFSG.SectionRank.pRank_mono hr.one_lt hXM
  have hloc := CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_localRank r hr.one_lt S.M
    S.witness.maxLocal.1
  have hev := CFSG.RankThreeCoreUniqueness.Helpers.rankThreeLocalRank_le_evenRank (G := G) r hr hr2
  rw [hS.rank] at hev
  have hrank : CFSG.Open.pRank r X ≤ 3 := by omega
  have hdisj : CFSG.Open.pRank r X ≤ 2 ∨ r + 1 < p := by
    by_contra hc
    push Not at hc
    obtain ⟨h3, hpr1⟩ := hc
    have h3M : 3 ≤ CFSG.Open.pRank r S.M := by omega
    have hr7 : r < 7 := by
      by_contra h7
      push Not at h7
      exact hrσ (mem_sigmaOf_of_three_le_pRank hS hUC S.witness.maxLocal hr h7 h3M)
    have hp35 : p = 3 ∧ r = 5 := by
      have h4 : ¬ Nat.Prime 4 := by decide
      have h6 : ¬ Nat.Prime 6 := by decide
      have := hpP.two_le
      have := hr.two_le
      interval_cases r <;> interval_cases p <;>
        first
        | omega
        | exact absurd hr h4
        | exact absurd hr h6
        | exact absurd hpP h4
        | exact absurd hpP h6
        | exact ⟨rfl, rfl⟩
    obtain ⟨rfl, rfl⟩ := hp35
    have := CFSG.LocalAnalysis.RankThreeTheoremC.rankThreeLocalRank_lt_three_of_sigmaA_three
      hS.rank hp.1 Nat.prime_five (by norm_num)
    omega
  exact UC6R77.rankThreeGamma_le_of_rank_bound hp2 hr2 hpr hsp
    (r76Sig_dataOfSetup hSE hSE3 hS S p hp hp2 hsp) hXM hXp hnc hexp hcl hrank hdisj h2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three
