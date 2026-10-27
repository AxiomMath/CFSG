module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2D4Out
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2D4Section

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22


theorem triD4OuterThreeRank_holds : TriD4OuterThreeRank := by
  intro X _ _ p hp hp7 hX α hα3 hα
  obtain ⟨J, E, -, -, -, hEJ, hE, hEc⟩ :=
    triD4OuterThree_exists_component_plane hp hp7 hX α hα3 hα
  exact CFSG.SectionRank.le_pRank hp.one_lt (hEJ.trans (Subgroup.map_subtype_le J)) hE hEc

end CFSG.LocalAnalysis.UniquenessCase.UC22
