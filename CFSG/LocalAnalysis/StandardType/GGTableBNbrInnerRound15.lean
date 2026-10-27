module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerRound15Label
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelNbrInner

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Certs

theorem ggTableBNbrInnerInputOn_round14Exc_of_round15 (hR : GGTwE6ThreeNbrRankInput)
    (h : GGTableBNbrInnerInputOn GGTableBNbrInnerRound15ExcLabel) :
    GGTableBNbrInnerInputOn GGTableBNbrInnerRound14ExcLabel := by
  have h12 := (h.or E6ThreeModel.ggTableBNbrInnerInputOn_e6Div).or
    (E6ThreeModel.ggTableBNbrInnerInputOn_twE6Three hR)
  refine GGTableBNbrInnerInputOn.mono (fun p lab hlab => ?_) h12
  by_cases h1 : GGTableBE6DivLabel p lab
  · exact Or.inl (Or.inr h1)
  · by_cases h2 : GGTableBTwE6ThreeLabel p lab
    · exact Or.inr h2
    · exact Or.inl (Or.inl ⟨hlab, h1, h2⟩)

end Certs

end CFSG.StandardType

end
