module

public import CFSG.LocalAnalysis.StandardType.GGWPlusNarrow5Defs
public import CFSG.LocalAnalysis.StandardType.GGWPlusTwE6Label

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggL48TableBKnownFormsRestRkOpen4_of_open5
    (h : GGL48TableBKnownFormsRestRkOpen5) : GGL48TableBKnownFormsRestRkOpen4 := by
  obtain ⟨h1, h2, h3, h4, h5, h8⟩ := h
  refine ⟨h1, h2, h3, h4, h5, ?_⟩
  intro p lab hp hlab hs hv hrow
  rcases hrow with hrow | hrow
  · exact h8 p lab hp hlab hs hv hrow
  · obtain ⟨ht, rfl, h3'⟩ := hrow
    have hr : GGL48TB0Rank lab = 6 := by simp [GGL48TB0Rank, ht]
    refine (largeEvenLabelAll_wplusRk_twE6_three hlab ht h3').mono fun _ _ _ _ hw => Or.inr ?_
    rw [hr]
    exact hw

end CFSG.StandardType
