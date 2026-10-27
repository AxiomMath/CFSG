module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenLinTwoNarrowDefs
public import CFSG.LocalAnalysis.StandardType.GGTorusGenLinTwoLabel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggL48TBForm4RestTwE6_of_restTwoA (h : GGL48TBForm4RestTwoA) : GGL48TBForm4RestTwE6 := by
  intro p lab hp hlab hS hv h0 hA hT hU hE
  by_cases hB : GGL48TBTwoARow p lab
  · obtain ⟨htag, hl, hn, hp3⟩ := hB
    have hl5 : 5 ≤ lab.rank := by
      by_contra hlt
      exact hv (Or.inr (Or.inr (Or.inl ⟨hp3, hn, Or.inl ⟨htag, by omega⟩⟩)))
    exact largeEvenLabelAll_torusGenTableB_linTwo hp hlab ⟨htag, hl5, hn, hp3⟩
  · exact h p lab hp hlab hS hv h0 hA hT hU hE hB

end CFSG.StandardType
