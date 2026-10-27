module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcNarrow19Defs
public import CFSG.LocalAnalysis.StandardType.GGTableBExcNarrow18
public import CFSG.LocalAnalysis.StandardType.GGTableBE6CoverLabel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggL48TableBKnownFormsRestRkOpen18_of_open19
    (h : GGL48TableBKnownFormsRestRkOpen19) : GGL48TableBKnownFormsRestRkOpen18 := by
  obtain ⟨h1, h4, h5⟩ := h
  refine ⟨?_, h4, h5⟩
  intro p lab hp hlab hS hv hD hT hA hA2 hTw hI hTwo
  by_cases hB : GGL48TBE6Row p lab
  · exact largeEvenLabelAll_coverP_E6 hp hlab hB
  · exact h1 p lab hp hlab hS hv hD hT hA hA2 hTw hI hTwo hB

end CFSG.StandardType
