module

public import CFSG.LocalAnalysis.UniquenessCase.UC7R71
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three

open Subgroup CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem pRank_le_three_dataOfSetup (hS : Standing G) (S : Setup G) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) {X : Subgroup G} (hXM : X ≤ S.M) : CFSG.Open.pRank q X ≤ 3 := by
  have h2 := CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank q hq hq2 S.M
    S.witness.maxLocal.1
  rw [hS.rank] at h2
  exact (CFSG.SectionRank.pRank_mono hq.one_lt hXM).trans h2

theorem r71_dataOfSetup (hS : Standing G) (S : Setup G)
    (h63 : UC6.R6_3 (dataOfSetup hS S)) : F07.R71 (dataOfSetup hS S) :=
  F07.r71_of_r6_3 _ h63 fun q hq hq2 X hXM _ h4 => by
    have := pRank_le_three_dataOfSetup hS S hq hq2 hXM
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three
