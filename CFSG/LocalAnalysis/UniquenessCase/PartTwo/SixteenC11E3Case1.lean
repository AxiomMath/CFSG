module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3Tools

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

section Certified


theorem s1611e3_normalizer_le_of_case1_v1eq {D : Data G} (h : S1611e3Std D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV)
    (h1 : Case168_1 D V₀ V hV L) (hv : v1Sub D.M V₀ V hV L = V₀) :
    normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
  have hp3 : 3 ∈ D.sig := by
    rw [h1.2.2.2]
    exact Set.mem_singleton 3
  have hTI : S16C11TI D V₀ V :=
    s1611e3_tiConj_of_pRank_lt h hc.setting.hyp16 hp3 (s16n9b_case1_pRank_lt D hV h1)
  have ha : aBar D.M V₀ V hV < 2 :=
    (s16t_aBar_lt_two_and_three_le_mBar_of_v1Sub_eq D hc h1 hv).1
  refine s1611e3_normalizer_le_of_routeA_empty h hc hTI (fun E hE _ => ?_) hp3
  have hle : 2 ≤ aBar D.M V₀ V hV := by
    simpa [aBar, calABar] using
      CFSG.Quasithin.E3.le_aParam_of_mem_aSet (W := Vtil V₀ V hV) (by norm_num) hE
  omega

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
