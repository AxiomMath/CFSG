module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KU3CensusU3
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KU3SU3L2Fix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

theorem kU3SU3L2Fix_holds : KU3SU3L2Fix := by
  intro F _ _ f m hF hf hm L hL
  exact exists_isL2_le_of_isL2_statedSU F f m hF hf hm L hL

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

end
