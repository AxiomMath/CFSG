module

public import CFSG.RankThree.PartTwo.Sec4.Census.TripleCoverF2
public import CFSG.RankThree.PartTwo.Sec4.Census.TripleCoverF5

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)

section Residual

theorem tripleCoverSporadicResidual : TripleCoverSporadicResidual :=
  ⟨tripleCoverSporadicRankFour_Ly, tripleCoverSporadicRankFour_Co3,
    tripleCoverSporadicRankFour_Co2, tripleCoverSporadicRankFour_HN,
    tripleCoverSporadicRankFour_Th⟩

end Residual

end CFSG.RankThree.PartTwo.Sec4.Census
