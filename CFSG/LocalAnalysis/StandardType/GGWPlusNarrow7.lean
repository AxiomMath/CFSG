module

public import CFSG.LocalAnalysis.StandardType.GGWPlusNarrow7Defs
public import CFSG.LocalAnalysis.StandardType.GGWPlusD4Split

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggL48TableBKnownFormsRestRkOpen6_of_open7 (h : GGL48TableBKnownFormsRestRkOpen7) :
    GGL48TableBKnownFormsRestRkOpen6 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, ?_, h4, h5⟩
  intro p lab hp hlab hs hv hd
  by_cases hn : lab.n = 1
  · exact h3 p lab hp hlab hs hv hd hn
  · have htag : lab.tag = .D := hd.1
    have hpn : p ∣ 2 ^ lab.n - 1 := by
      rcases hs with ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨hn1, _⟩
      · exact h
      · exact absurd (by rw [htag]; trivial) h
      · rcases h with h | h <;> rw [htag] at h <;> exact absurd h (by decide)
      · exact absurd hn1 hn
    exact largeEvenLabelAll_irredTableB_D4_split hp hlab hd hpn

end CFSG.StandardType
