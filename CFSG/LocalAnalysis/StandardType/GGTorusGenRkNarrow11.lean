module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkNarrow11Defs
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkLabel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggL48TableBKnownFormsRestRkOpen10_of_open11
    (h : GGL48TableBKnownFormsRestRkOpen11) : GGL48TableBKnownFormsRestRkOpen10 := by
  obtain ⟨h1, h4, h5⟩ := h
  refine ⟨h1, h4, ?_⟩
  intro p lab hp hlab hS hv hRow
  rcases hRow with hA | hE
  · have hne : lab.tag ≠ .twE6 := by rw [hA.1]; decide
    have hrank : GGL48TB0Rank lab = lab.rank := by
      unfold GGL48TB0Rank
      rw [if_neg hne]
    simpa [hrank] using largeEvenLabelAll_torusGenRk_twA_dvd hp hlab hv hA
  · exact h5 p lab hp hlab hS hv hE

end CFSG.StandardType
