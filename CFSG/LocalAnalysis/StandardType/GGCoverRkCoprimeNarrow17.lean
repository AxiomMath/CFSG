module

public import CFSG.LocalAnalysis.StandardType.GGCoverRkCoprimeNarrow17Defs
public import CFSG.LocalAnalysis.StandardType.GGCoverRkCoprime

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggL48TableBKnownFormsRestRkOpen16_of_open17
    (h : GGL48TableBKnownFormsRestRkOpen17) : GGL48TableBKnownFormsRestRkOpen16 := by
  obtain ⟨h1, h4, h5⟩ := h
  refine ⟨?_, h4, h5⟩
  intro p lab hp hlab hS hv hD hT hA hA2
  by_cases hB : GGL48TBTwistedARow p lab
  · obtain ⟨htag, hl, hpn, hpd⟩ := hB
    exact largeEvenLabelAll_coverP_twA_coprime hp hlab htag hl hpn hpd
  · exact h1 p lab hp hlab hS hv hD hT hA hA2 hB

end CFSG.StandardType
