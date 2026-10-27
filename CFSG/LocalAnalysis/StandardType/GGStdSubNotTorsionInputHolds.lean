module

public import CFSG.LocalAnalysis.StandardType.GGTorsionExcNoF4
public import CFSG.LocalAnalysis.StandardType.GGTorsionExc
import CFSG.LocalAnalysis.StandardType.GGTorsionTarget
import CFSG.LocalAnalysis.StandardType.GGTorsionClasses
import CFSG.LocalAnalysis.StandardType.GGTorsionTwA
import CFSG.LocalAnalysis.StandardType.GGTorsionBCDClass
import CFSG.LocalAnalysis.StandardType.GGTorsionTwF4

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggStdSubNotTorsionInput_holds
    : GGStdSubNotTorsionInput :=
  ggStdSubNotTorsionInput_of_known
    (ggTorsionKnown_of_classes ggTorsionKnownOver_ambA ggTorsionKnownOver_ambBCD
      (ggTorsionKnownOver_exc_of_noF4 ggExcNoF4Known_holds) ggTorsionKnownOver_small)

end CFSG.StandardType
