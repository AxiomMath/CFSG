module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s168e3_row162_6 {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (h : Case162_6 D V₀ V hV L) : Case167_4 D V₀ V hV L := by
  have hw := s15_Three_wStar_eq_top D c.std.h1217 c.setting.hyp151 hV c.ne h.2.2.1
  refine ⟨h.1, ?_, h.2.2.2.1⟩
  have := h.2.1
  rwa [hw] at this

theorem s168e3_row162_9 {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (h : Case162_9 D V₀ V hV L) : Case167_8 D V₀ V hV L := by
  have hw := s15_Three_wStar_eq_top D c.std.h1217 c.setting.hyp151 hV c.ne h.2.2.1
  refine ⟨h.1, ?_, h.2.2.2⟩
  have h8 : rk ↥(wStar D.M V₀ V hV L) = 8 := h.2.1
  rwa [hw] at h8

theorem s168e3_row163_2 {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (h165 : R16_5 D) (h : Case163_2 D V₀ V hV L) :
    Case167_6 D V₀ V hV L := by
  have hwT := wTil_eq_top_of_case163_2 c.conc h.2.2
  have hnat := h.2.1
  rw [hwT] at hnat
  exact ⟨h.1, hnat, (h165 V₀ V L hV c.setting c.ne c.conc h.1).1⟩

theorem s168e3_row163_7 {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (h : Case163_7 D V₀ V hV L) : Case168_7 D V₀ V hV L :=
  h

theorem s168e3_row163_8F {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (h : Case163_8F D V₀ V hV L) : Case167_7F D V₀ V hV := by
  have hwT := wTil_eq_top_of_case163_2 c.conc h.2.2.1
  have hnat := h.2.1
  rw [hwT] at hnat
  exact ⟨h.1, hnat, h.2.2.2⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
