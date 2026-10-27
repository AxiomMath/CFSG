module

public import CFSG.LocalAnalysis.StandardType.GGWPlusNarrow8Defs
public import CFSG.LocalAnalysis.StandardType.GGWPlusD4TwoLabel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggL48TableBKnownFormsRestRkOpen7_of_open8
    (h : GGL48TableBKnownFormsRestRkOpen8) : GGL48TableBKnownFormsRestRkOpen7 := by
  obtain ⟨h1, h2, h4, h5⟩ := h
  refine ⟨h1, h2, ?_, h4, h5⟩
  intro p lab _ _ _ _ hd hn
  obtain rfl : p = 3 := hd.2.2
  exact largeEvenLabelAll_irredTableB_D4_two hd hn

end CFSG.StandardType
