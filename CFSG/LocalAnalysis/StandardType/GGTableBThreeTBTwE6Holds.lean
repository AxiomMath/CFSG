module

public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6Q8
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6RankFive
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeSCFourOdd
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeSCFourOddHolds
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelInputs
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelHoldsBoth
public import CFSG.LocalAnalysis.StandardType.GGTwE6TInHolds
public import CFSG.LocalAnalysis.StandardType.GGTwE6LemmaKFinal
public import CFSG.LocalAnalysis.StandardType.GGTwE6R5Holds

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggTwE6ThreeSCFourNotTwoLocalOddInput_holds :
    GGTwE6ThreeSCFourNotTwoLocalOddInput :=
  ggTwE6ThreeSCFourNotTwoLocalOddInput_of_kga1
    NoOffTwE6Three.ggTwE6ThreeTwoLocalInnToralInput_holds
    TwE6LemmaK.ggTwE6ThreeToralTypeMinusOneInput
    ggTwE6ThreeNoRankSixInput_holds

theorem ggTwE6ThreeSCFourNotTwoLocalInput_holds :
    GGTwE6ThreeSCFourNotTwoLocalInput :=
  ggTwE6ThreeSCFourNotTwoLocalInput_of_odd ggTwE6ThreeSCFourNotTwoLocalOddInput_holds

theorem ggTwE6ThreeBstarRankInput_holds : GGTwE6ThreeBstarRankInput :=
  ggTwE6ThreeBstarRankInput_of_known ggTwE6ThreeSCFourNotTwoLocalInput_holds

end CFSG.StandardType
