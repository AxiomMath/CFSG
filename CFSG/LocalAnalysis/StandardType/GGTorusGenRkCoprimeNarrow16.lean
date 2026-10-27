module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkCoprimeNarrow16Defs
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkCoprime

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggL48TableBKnownFormsRestRkOpen15_of_open16
    (h : GGL48TableBKnownFormsRestRkOpen16) : GGL48TableBKnownFormsRestRkOpen15 := by
  obtain ⟨h1, h4, h5⟩ := h
  refine ⟨h1, ?_, h5⟩
  intro p lab hp hlab hS hv hT hA
  by_cases hB : GGL48TBTwistedARow p lab
  · obtain ⟨htag, hl, hpn, hpd⟩ := hB
    exact largeEvenLabelAll_torusGenTableB_twA_coprime hp hlab htag hl hpn hpd
  · exact h4 p lab hp hlab hS hv hT hA hB

end CFSG.StandardType
