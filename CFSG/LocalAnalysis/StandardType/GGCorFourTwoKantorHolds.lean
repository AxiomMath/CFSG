module

public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoKantor
public import CFSG.LocalAnalysis.StandardType.McLaughlinOddKantorBlocks

public section

namespace CFSG.StandardType

theorem ggKantorReductionInput_holds : GGKantorReductionInput :=
  fun _ _ hp _ _ _ _ A hA => McLaughlinOdd.kantor_blocks hp A hA

end CFSG.StandardType
