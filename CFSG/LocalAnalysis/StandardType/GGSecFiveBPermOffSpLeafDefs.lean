module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermLinNbrDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermProperQTwoDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBJoinDefs

public section

namespace CFSG.StandardType

section Inputs


@[expose] def GGSecFiveBPermLinSU6BalInput : Prop :=
  GGLBalanceInput → GGSecFiveBPermLinSU6Input

@[expose] def GGSecFiveBPermProperQTwoNbrRedInput : Prop :=
  GGTBFixInput → GGResXDichotomyInput → GGTCJKnown → GGNbrTablePNbrInputNarrow →
    GGForkA8NotReflInput → GGRawInnFieldInput → GGRawInndiagIsoInput →
    GGResNbrFixCentralizesInput → GGLBalanceInput → GGSecFiveBProperRootInput → GGTBTorAll →
    GGTBTorLiftRows → GGNbrSubcomponentInput → GGStdSubPrimeInput → GGTwE6ThreeNbrRankInput →
    GGLabelCenterPCyclicInput → GGSecFiveBPermProperQTwoNbrInput

@[expose] def GGSecFiveBPermProperQTwoSpPairMpInput : Prop :=
  GGInnerDiagMpInput → GGSecFiveBPermProperQTwoSpPairInput

end Inputs

end CFSG.StandardType

end
