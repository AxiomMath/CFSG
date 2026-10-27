module

public import CFSG.LocalAnalysis.StandardType.GGTwE6LangThree
public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwelveDefs

public section

namespace CFSG.StandardType

@[expose] def GGTableBTwE6Round12Lang : Prop :=
  GGTwE6FieldCentInvInput ∧ GGTwE6ThreeDeltaTwoInput ∧ GGTwE6ThreeRootKernelInput ∧
    GGTwE6ThreeFieldInput ∧ GGTwE6EndNodeInnerInput ∧ GGTwE6EndNodeThreeInput

section Round

theorem ggTableBTwE6Round12_of_lang (h : GGTableBTwE6Round12Lang) : GGTableBTwE6Round12 :=
  ⟨h.1, ggTwE6ThreeInndiagRankInput_holds, ggTwE6ThreeCoverRankInput_holds, h.2.1, h.2.2.1,
    h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

end Round

end CFSG.StandardType
