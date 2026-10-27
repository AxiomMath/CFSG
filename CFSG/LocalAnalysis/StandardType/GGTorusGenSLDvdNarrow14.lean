module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenSLDvdNarrow14Defs
public import CFSG.LocalAnalysis.StandardType.GGTorusGenSLDvd

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggL48TableBKnownFormsRestRkOpen13_of_open14 (h : GGL48TableBKnownFormsRestRkOpen14) :
    GGL48TableBKnownFormsRestRkOpen13 := by
  obtain ⟨h1, h4, h5⟩ := h
  refine ⟨h1, ?_, h5⟩
  intro p lab hp hlab hS hv hT hA
  by_cases hB : GGL48TBTypeARow p lab
  · obtain ⟨htag, hl, hpn⟩ := hB
    exact largeEvenLabelAll_torusGenTableB_typeA hp hlab htag hl hpn
  · exact h4 p lab hp hlab hS hv hT hB

end CFSG.StandardType
