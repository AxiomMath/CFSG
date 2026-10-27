module

public import CFSG.LocalAnalysis.StandardType.GGCoverSLNarrow13Defs
public import CFSG.LocalAnalysis.StandardType.GGCoverSLPSL
public import CFSG.LocalAnalysis.StandardType.GGTorusGenSLNarrow12

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggL48TableBKnownFormsRestRkOpen12_of_open13 (h : GGL48TableBKnownFormsRestRkOpen13) :
    GGL48TableBKnownFormsRestRkOpen12 := by
  obtain ⟨h1, h4, h5⟩ := h
  refine ⟨?_, h4, h5⟩
  intro p lab hp hlab hS hv hD hT
  by_cases hA : GGL48TBTypeARow p lab
  · obtain ⟨htag, hl, hpn⟩ := hA
    exact largeEvenLabelAll_coverP_typeA hp hlab htag hl hpn
  · exact h1 p lab hp hlab hS hv hD hT hA

end CFSG.StandardType
