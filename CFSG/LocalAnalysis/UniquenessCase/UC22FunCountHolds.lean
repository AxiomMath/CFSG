module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F3Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22FunCountMany
import CFSG.LocalAnalysis.UniquenessCase.UC22FunCountTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

theorem kFunCount_holds :
    KFunCount := by
  intro X _ _ _ t n p f hp hp2 hadm hX P
  constructor
  · intro htwo
    exact ncard_funSet_eq_two_of_funTwoType hp hp2 hadm hX htwo P
  · intro hmany
    exact three_le_ncard_funSet_of_funManyType hp hp2 hadm hX hmany P

end CFSG.LocalAnalysis.UniquenessCase.UC22
