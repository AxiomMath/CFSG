module

public import CFSG.LocalAnalysis.StandardType.GGCoverRkNarrow9Defs
public import CFSG.LocalAnalysis.StandardType.GGCoverRkUnitLabel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggL48TableBKnownFormsRestRkOpen8_of_open9
    (h : GGL48TableBKnownFormsRestRkOpen9) : GGL48TableBKnownFormsRestRkOpen8 := by
  obtain ⟨h1, h2E, h4, h5⟩ := h
  refine ⟨h1, ?_, h4, h5⟩
  intro p lab hp hlab hS hv hrow
  rcases hrow with hA | hE
  · have hne : ¬ (lab.tag = .twE6) := by
      rw [hA.1]
      decide
    have hrank : GGL48TB0Rank lab = lab.rank := by
      unfold GGL48TB0Rank
      rw [if_neg hne]
    simpa [hrank] using largeEvenLabelAll_coverPRk_twA_dvd hp hlab hv hA
  · exact h2E p lab hp hlab hS hv hE

end CFSG.StandardType
