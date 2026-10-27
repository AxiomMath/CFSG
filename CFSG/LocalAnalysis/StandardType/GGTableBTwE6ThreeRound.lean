module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Three
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6PerInput
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6RankOuter

public section

namespace CFSG.StandardType

section Round


theorem ggBstarInputOn_round6_of_twE6Inputs (hF : GGTwE6FieldCentInvInput)
    (hX : GGTwE6ThreeInndiagRankInput) (hC : GGTwE6ThreeCoverRankInput)
    (hD : GGTwE6ThreeDeltaTwoInput) (hB1 : GGTwE6ThreeRootKernelInput)
    (hB2 : GGTwE6ThreeFieldInput) : GGBstarInputOn GGTableBOtherRound6 :=
  ggBstarInputOn_round6_of_twE6 TwE6Per.ggTwE6TorusLiftInput_holds
    (ggTwE6BstarInput_of_fieldCentInv hF) (ggTwE6BstarThreeInput_of_inputs hX hC hD hB1 hB2)

theorem ggStdSubPreInputOn_round6_of_twE6Inputs
    (hI : GGTwE6EndNodeInnerInput) (hE3 : GGTwE6EndNodeThreeInput) :
    GGStdSubPreInputOn GGTableBOtherRound6 :=
  ggStdSubPreInputOn_round6_of_twE6 TwE6Per.ggTwE6TorusLiftInput_holds
    (ggTwE6EndNodeInput_of_inner hI) hE3

end Round

end CFSG.StandardType
