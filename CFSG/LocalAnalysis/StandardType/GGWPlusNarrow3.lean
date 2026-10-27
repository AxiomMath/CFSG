module

public import CFSG.LocalAnalysis.StandardType.GGWPlusNarrow3Defs
public import CFSG.LocalAnalysis.StandardType.GGWPlusLabel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggL48TableBKnownFormsRestRkOpen2_of_open3 (h : GGL48TableBKnownFormsRestRkOpen3) :
    GGL48TableBKnownFormsRestRkOpen2 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h8⟩ := h
  refine ⟨h1, h2, h3, h4, h5, ?_, h8⟩
  intro p lab hp hlab hs hv hd hf ht ho
  rcases ho with ho | ho
  · exact (largeEvenLabelAll_wplus_typeA_dvd hp hlab ⟨ho.1, ho.2.2, ho.2.1⟩).mono
      fun _ _ _ _ h => Or.inr h
  · exact h6 p lab hp hlab hs hv hd hf ht ho

end CFSG.StandardType
