module

public import CFSG.LocalAnalysis.StandardType.GGCoverSLTwoNarrow15Defs
public import CFSG.LocalAnalysis.StandardType.GGCoverSLTwoPSL

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggL48TableBKnownFormsRestRkOpen14_of_open15 (h : GGL48TableBKnownFormsRestRkOpen15) :
    GGL48TableBKnownFormsRestRkOpen14 := by
  obtain ⟨h1, h4, h5⟩ := h
  refine ⟨?_, h4, h5⟩
  intro p lab hp hlab hS hv hD hT hA
  by_cases hB : GGL48TBTwoARow p lab
  · obtain ⟨htag, hl, hn, hp3⟩ := hB
    exact largeEvenLabelAll_coverP_typeA_two hp (by omega) htag hl hn
  · exact h1 p lab hp hlab hS hv hD hT hA hB

end CFSG.StandardType
