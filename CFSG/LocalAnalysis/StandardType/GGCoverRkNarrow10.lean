module

public import CFSG.LocalAnalysis.StandardType.GGCoverRkNarrow10Defs
public import CFSG.LocalAnalysis.StandardType.GGCoverRkTwE6Label

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggL48TableBKnownFormsRestRkOpen9_of_open10
    (h : GGL48TableBKnownFormsRestRkOpen10) : GGL48TableBKnownFormsRestRkOpen9 := by
  obtain ⟨h1, h4, h5⟩ := h
  refine ⟨h1, ?_, h4, h5⟩
  intro p lab hp hlab hS hv hE
  obtain ⟨ht, rfl, h3⟩ := hE
  have hrank : GGL48TB0Rank lab = 6 := by
    unfold GGL48TB0Rank
    rw [if_pos ht]
  simpa [hrank] using largeEvenLabelAll_coverPRk_twE6_three (lab := lab) hlab ht h3

end CFSG.StandardType
