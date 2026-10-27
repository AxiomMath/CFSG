module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3Tools
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

section Certified


theorem s1611e3_v1_case1_aSet_empty (hGap : S1611e3V1SixGap) {D : Data G}
    (h : S1611e3Std D) {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D ⊥ V L hV) (hs : s15 D.M ⊥ V hV L = 1)
    (h1 : Case168_1 D ⊥ V hV L) (hV1 : v1Sub D.M ⊥ V hV L ≠ ⊥) :
    ∀ E ∈ calABar 2 D.M ⊥ V hV, False := by
  exact s1611e3_v1_case1_aSet_empty_core hGap h hc hs h1 hV1

theorem s1611e3_v1_hard_case1 (hGap : S1611e3V1SixGap) {D : Data G}
    (h : S1611e3Std D) {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D ⊥ V L hV) (hs : s15 D.M ⊥ V hV L = 1)
    (h1 : Case168_1 D ⊥ V hV L) (hV1 : v1Sub D.M ⊥ V hV L ≠ ⊥) :
    normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
  have hp3 : 3 ∈ D.sig := by
    rw [h1.2.2.2]
    exact Set.mem_singleton 3
  have hTI : S16C11TI D ⊥ V := by
    intro g _
    exact ⟨bot_inf_eq _, by rw [E3.conjSubgroup_bot, inf_bot_eq]⟩
  exact s1611e3_normalizer_le_of_routeA_empty h hc hTI
    (fun E hE _ => s1611e3_v1_case1_aSet_empty hGap h hc hs h1 hV1 E hE) hp3

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
