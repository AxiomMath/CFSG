module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case5
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3Ctx

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

section Certified


theorem s1611e3_normalizer_le_of_case5 {D : Data G} (h : S1611e3Std D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) (h5 : Case168_5 D V₀ V hV L) :
    normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M :=
  s16c11_normalizer_le_of_case5 D (h.in10 hc.setting.hyp16.hyp125) h.h1217
    (h.r16_10_2 hc.setting.hyp16.hyp125) hc (h.out10 hc) h5

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
