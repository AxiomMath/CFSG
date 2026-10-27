module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenSLNarrow12Defs
public import CFSG.LocalAnalysis.StandardType.GGTorusGenSLPSL
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkNarrow11

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggL48TableBKnownFormsRestRkOpen11_of_open12 (h : GGL48TableBKnownFormsRestRkOpen12) :
    GGL48TableBKnownFormsRestRkOpen11 := by
  obtain ⟨h1, h4, h5⟩ := h
  refine ⟨h1, ?_, h5⟩
  intro p lab hp hlab hS hv hT
  by_cases hA : GGL48TBTorusARow p lab
  · obtain ⟨htag, hl, hpn, hpd⟩ := hA
    exact largeEvenLabelAll_torusGenTableB_typeA_coprime hp hlab htag hl hpn hpd
  · exact h4 p lab hp hlab hS hv hT hA

end CFSG.StandardType
