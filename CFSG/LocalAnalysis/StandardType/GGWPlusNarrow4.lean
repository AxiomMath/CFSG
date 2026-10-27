module

public import CFSG.LocalAnalysis.StandardType.GGWPlusNarrow4Defs
public import CFSG.LocalAnalysis.StandardType.GGWPlusE6Label

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggL48TableBKnownFormsRestRkOpen3_of_open4
    (h : GGL48TableBKnownFormsRestRkOpen4) : GGL48TableBKnownFormsRestRkOpen3 := by
  obtain ⟨h1, h2, h3, h4, h5, h8⟩ := h
  refine ⟨h1, h2, h3, h4, h5, ?_, h8⟩
  intro p lab hp hlab hs hv hd hf ht ho
  obtain rfl : p = 3 := ho.2.1
  exact (largeEvenLabelAll_wplus_E6_three hlab ho).mono fun _ _ _ _ h => Or.inr h

end CFSG.StandardType
