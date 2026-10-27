module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3C6XA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3C6V0

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s1611e3_case6_l3_routeF {D : Data G} (h : S1611e3Std D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) (h6 : Case168_6 D V₀ V hV L)
    (hL3 : IsL3 ↥(lBar V₀ V hV L) 1) : S1611e3RouteF D V₀ V hV 3 :=
  s1611e3_case6_l3_routeF_data h hc h6 hL3

section Certified


theorem s1611e3_normalizer_le_of_case6 {D : Data G} (h : S1611e3Std D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) (h6 : Case168_6 D V₀ V hV L) :
    normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
  have hp3 : 3 ∈ D.sig := by
    rw [h6.2.2.2]
    exact Set.mem_singleton 3
  rcases h6.2.1 with ⟨hA5, -⟩ | ⟨hL3, -⟩
  · exact s1611e3_case6_a5_core h hc h6 hA5
  · exact s1611e3_normalizer_le_of_routeF_data h hc hp3 (s1611e3_case6_l3_routeF h hc h6 hL3)

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
