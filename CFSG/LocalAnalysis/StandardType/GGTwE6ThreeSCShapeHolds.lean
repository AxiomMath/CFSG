module

public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRankFiveAssembly
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeA2BlockTwo

public section

namespace CFSG.StandardType.NoOffTwE6Three


theorem ggTwE6ThreeRankFiveInput_holds : GGTwE6ThreeRankFiveInput :=
  ggTwE6ThreeRankFiveInput_of_a2Block a2BlockTwoInput_holds

theorem ggTwE6ThreeSCShapeInput_holds : GGTwE6ThreeSCShapeInput :=
  ggTwE6ThreeSCShapeInput_of_rankFive ggTwE6ThreeRankFiveInput_holds

end CFSG.StandardType.NoOffTwE6Three
