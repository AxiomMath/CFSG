module

public import CFSG.LocalAnalysis.StandardType.GGWPlusNarrow6Defs
public import CFSG.LocalAnalysis.StandardType.GGWPlusUnitLabel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggL48TableBKnownFormsRestRkOpen5_of_open6
    (h : GGL48TableBKnownFormsRestRkOpen6) : GGL48TableBKnownFormsRestRkOpen5 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, h3, h4, h5, ?_⟩
  intro p lab hp hlab hs hv hrow
  have hr : GGL48TB0Rank lab = lab.rank := by
    have ht : lab.tag ≠ .twE6 := by rw [hrow.1]; decide
    simp [GGL48TB0Rank, ht]
  refine (largeEvenLabelAll_wplusRk_twA_dvd hp hlab hv hrow).mono fun _ _ _ _ hw => Or.inr ?_
  rw [hr]
  exact hw

end CFSG.StandardType
