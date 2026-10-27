module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcNarrow20Defs
public import CFSG.LocalAnalysis.StandardType.GGTableBExcNarrow19
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6CoverLabel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggL48TableBKnownFormsRestRkOpen19_of_open20
    (h : GGL48TableBKnownFormsRestRkOpen20) : GGL48TableBKnownFormsRestRkOpen19 := by
  obtain ⟨h1, h4, h5⟩ := h
  refine ⟨?_, h4, h5⟩
  intro p lab hp hlab hS hv hD hT hA hA2 hTw hI hTwo hE6
  by_cases hB : GGL48TBTwE6Row p lab
  · exact largeEvenLabelAll_coverP_twE6 hp hlab hB
  · exact h1 p lab hp hlab hS hv hD hT hA hA2 hTw hI hTwo hE6 hB

end CFSG.StandardType
