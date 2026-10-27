module

public import CFSG.RankThree.PartOne.KP.SporadicTwoGroup
public import CFSG.Sporadic.Co2Schreier.Model
public import CFSG.RankThree.PartOne.KP.SporadicDefs

public section

namespace CFSG.RankThree.PartOne

open CFSG

theorem sporadicCoprimeRank_Co2 : SporadicCoprimeRank .Co2 := by
  intro T _ _ ⟨e⟩ p hp hp5 hpT
  obtain ⟨hfin, h2, -⟩ := Sporadic.Co2Schreier.AT_Co2_model_Schreier T e
  exact ElementaryRankAtMostOne.of_not_dvd_outer hp hpT
    (not_dvd_card_of_isPGroup_two hfin h2 hp hp5)

end CFSG.RankThree.PartOne
