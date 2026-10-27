module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67SmallKGCite
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67CentL3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67CentU3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small

theorem k67CentL3U3_holds : K67CentL3U3 := by
  intro J _ _ p f hS x hx
  rcases hS with ⟨hq, hL⟩ | ⟨hq, hU⟩
  · exact isCyclic_and_card_centralizer_of_lieModel_psl hq hL hx
  · exact isCyclic_and_card_centralizer_of_lieModel_psu hq hU hx

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small
