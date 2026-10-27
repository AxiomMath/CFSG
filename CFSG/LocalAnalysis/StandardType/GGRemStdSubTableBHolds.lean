module

public import CFSG.LocalAnalysis.StandardType.GGRemStdSubTableBOpen
import CFSG.LocalAnalysis.StandardType.GGTwE6NormSmallThree
import CFSG.LocalAnalysis.StandardType.GGTwE6NormSmallThreeSetup
import CFSG.LocalAnalysis.StandardType.GGTwE6CubeNodeCore
import CFSG.LocalAnalysis.StandardType.GGTwE6CorootCoreHolds
import CFSG.LocalAnalysis.StandardType.GGTwE6D5CoreHolds

public section

namespace CFSG.StandardType

open CFSG.Yardstones.M3f9567aba59d (GGRemainderStdSubTableB)


theorem ggRemainderStdSubTableB_proved : GGRemainderStdSubTableB :=
  ggRemainderStdSubTableB_of_open
    (SmallExc.ggTwE6NormSmallThreeInput_of_endNode TwE6NormThree.exists_endNode_data)
    (TwE6Cube.ggTwE6CubeNodeInput_of_cores TwE6RootAs.twE6CorootCore_holds
      TwE6RootAs.twE6D5Core_holds)

end CFSG.StandardType

end
