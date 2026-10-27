module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91Defs
import CFSG.Adapters.LieModelSimple
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviCenter
import CFSG.Quasithin.EmptyFaithful.R3c3Rank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R891Core

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi
  (center_eq_bot_of_simple_of_two_le_pRank)

theorem two_le_pRank_three_quot_center_of_sl3Two {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (hn : 2 ≤ n) (h : R891SL3Two Y n) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Y ⧸ center Y)) := by
  unfold R891SL3Two at h
  rcases h with ⟨rfl, -⟩ | ⟨-, hEven, hcov⟩ | ⟨-, hOdd, hcov⟩
  · omega
  · exact CFSG.Quasithin.R3c3.two_le_pRank_three_isPSL_three_two_even hEven
      (CFSG.Blueprint.LieModel.statedClassicalModel hcov.2.2 (by decide))
  · exact CFSG.Quasithin.R3c3.two_le_pRank_three_isPSU_two_odd hOdd
      (CFSG.Blueprint.LieModel.statedClassicalModel hcov.2.2 (by decide))

theorem two_le_pRank_three_quot_center_of_l3Pi {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (h : R891L3Pi Y n) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Y ⧸ center Y)) := by
  unfold R891L3Pi at h
  rcases h with ⟨hEven, hLie⟩ | ⟨hOdd, hLie⟩
  · have hS : IsSimpleGroup Y :=
      CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hLie
    have hrank : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y) :=
      CFSG.Quasithin.R3c3.two_le_pRank_three_isPSL_three_two_even hEven
        (CFSG.Blueprint.LieModel.statedClassicalModel hLie (by decide))
    have hZ : Subgroup.center Y = ⊥ := center_eq_bot_of_simple_of_two_le_pRank Nat.prime_three hrank
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3)
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)]
    exact hrank
  · have hS : IsSimpleGroup Y :=
      CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hLie
    have hrank : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y) :=
      CFSG.Quasithin.R3c3.two_le_pRank_three_isPSU_two_odd hOdd
        (CFSG.Blueprint.LieModel.statedClassicalModel hLie (by decide))
    have hZ : Subgroup.center Y = ⊥ := center_eq_bot_of_simple_of_two_le_pRank Nat.prime_three hrank
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3)
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)]
    exact hrank

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R891Core
