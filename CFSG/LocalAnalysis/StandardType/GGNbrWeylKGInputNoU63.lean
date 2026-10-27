module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylCompDefs

public section

namespace CFSG.StandardType

@[expose] def GGNbrWeylKGInputNoU63 : Prop :=
  GGNbrKGE6ThreeDvd ∧ GGNbrKGTwE6ThreeDvd ∧ GGNbrKGTwE6AddLarge ∧ GGNbrKGE7SmallAdd ∧
    GGNbrKGE8SmallAdd ∧ GGNbrKGF4ThreeAdd ∧ GGNbrKGFieldE6 ∧
    GGNbrKGFieldTwE6ThreeDvd ∧ GGNbrKGFieldTwE6AddLarge ∧ GGNbrKGFieldE7 ∧ GGNbrKGFieldE8 ∧
    GGNbrKGFieldF4 ∧ GGNbrKGFieldUnitSix ∧ GGNbrKGFieldTriD4Two

theorem ggNbrWeylKGInput_of_noU63 (hU : GGNbrKGUnitSixThree) (h : GGNbrWeylKGInputNoU63) :
    GGNbrWeylKGInput := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, hU, h8, h9, h10, h11, h12, h13, h14, h15⟩

end CFSG.StandardType
