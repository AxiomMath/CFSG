module

public import CFSG.LocalAnalysis.StandardType.GGExcTwoCompListsRE
import CFSG.LocalAnalysis.StandardType.GGK0CompREMult
public import CFSG.LocalAnalysis.StandardType.GGK0ExcB3Holds

public section

namespace CFSG.StandardType.E7TwoThree


theorem ggE7TwoThreeComp_holds : GGE7TwoThreeComp :=
  ggE7TwoThreeComp_of_K0RE (ggK0CompRE_of_mult
    (ggK0CompREMult_of_excB GGK0ExcB3Prod.ggK0ExcB3_holds.toB2.toExcB))

end CFSG.StandardType.E7TwoThree
