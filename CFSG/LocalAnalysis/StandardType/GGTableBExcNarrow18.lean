module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcNarrow18Defs
public import CFSG.LocalAnalysis.StandardType.GGTableBExcCoverLabelExc

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggL48TableBKnownFormsRestRkOpen17_of_open18
    (h : GGL48TableBKnownFormsRestRkOpen18) : GGL48TableBKnownFormsRestRkOpen17 := by
  obtain ⟨h1, h4, h5⟩ := h
  refine ⟨?_, h4, h5⟩
  intro p lab hp hlab hS hv hD hT hA hA2 hTw
  by_cases hB : GGL48TBExcInnRow p lab ∨ GGL48TBExcTwoRow p lab
  · exact largeEvenLabelAll_coverP_excInn hp hlab hB
  · exact h1 p lab hp hlab hS hv hD hT hA hA2 hTw (fun hI => hB (Or.inl hI)) (fun hI => hB (Or.inr hI))

end CFSG.StandardType
