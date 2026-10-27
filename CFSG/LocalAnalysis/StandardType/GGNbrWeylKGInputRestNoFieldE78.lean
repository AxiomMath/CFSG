module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylCompDefs

public section

namespace CFSG.StandardType

@[expose] def GGNbrWeylKGInputRestNoFieldE78 : Prop :=
  GGNbrKGF4ThreeAdd ∧ GGNbrKGFieldE6 ∧ GGNbrKGFieldTwE6ThreeDvd ∧ GGNbrKGFieldTwE6AddLarge ∧
    GGNbrKGFieldF4 ∧ GGNbrKGFieldUnitSix ∧ GGNbrKGFieldTriD4Two

end CFSG.StandardType
