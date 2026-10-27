module

public import CFSG.RankThree.PartOne.KP.SporadicTwoGroup
public import CFSG.Sporadic.Co2Schreier.Model
public import CFSG.Sporadic.Schreier.Co1CatalogSchreier
public import CFSG.RankThree.PartOne.KP.SporadicDefs

public section

namespace CFSG.RankThree.PartOne

open CFSG

theorem sporadicCoprimeRank_Co1 : SporadicCoprimeRank .Co1 := by
  intro T _ _ ⟨e⟩ p hp hp5 hpT
  obtain ⟨-, hfin, h2, -⟩ := Sporadic.Co1Schreier.catalog_schreier_of_inputs.{0}
    fun K _ e => Sporadic.Co2Schreier.AT_Co2_model_Schreier K e
  refine ElementaryRankAtMostOne.of_not_dvd_outer hp hpT ?_
  rw [card_outer_eq_of_mulEquiv e]
  exact not_dvd_card_of_isPGroup_two hfin h2 hp hp5

end CFSG.RankThree.PartOne
