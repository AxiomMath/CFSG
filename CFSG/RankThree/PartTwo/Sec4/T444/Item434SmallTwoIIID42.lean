module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIIDefs

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores

namespace Item434SmallTwoIII

theorem chevalleyExceptionalModel_of_d42 {X : Type} [Group X] (hX : IsSmallTwoD42 X) :
    CFSG.Blueprint.ChevalleyExceptionalModel X .trialityD4 2 1 := by
  obtain ⟨q, hq, hq2, hq1, ⟨e⟩⟩ := hX
  have h := Census.bridgeExceptional46.trialityD4 q hq hq2
  rw [hq1] at h
  exact CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv e h

end Item434SmallTwoIII

end CFSG.RankThree.PartTwo.Sec4
