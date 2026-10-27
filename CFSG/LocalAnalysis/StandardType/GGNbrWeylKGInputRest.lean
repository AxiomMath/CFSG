module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylCompDefs

public section

namespace CFSG.StandardType

@[expose] def GGNbrWeylKGInputRest : Prop :=
  GGNbrKGF4ThreeAdd ∧ GGNbrKGFieldE6 ∧ GGNbrKGFieldTwE6ThreeDvd ∧ GGNbrKGFieldTwE6AddLarge ∧
    GGNbrKGFieldE7 ∧ GGNbrKGFieldE8 ∧ GGNbrKGFieldF4 ∧ GGNbrKGFieldUnitSix ∧
    GGNbrKGFieldTriD4Two

end CFSG.StandardType
