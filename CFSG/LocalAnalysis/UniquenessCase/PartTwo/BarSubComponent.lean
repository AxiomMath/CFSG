module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyThreeOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyFour

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem barSub_subgroupOf_mbar_normal {M L V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hLM : L ≤ M) (hMN : M ≤ normalizer (L : Set G)) :
    ((barSub V₀ V hV L).subgroupOf (Mbar M V₀ V hV)).Normal := by
  refine ⟨fun n hn m => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
    TwelveEighteen.conj_mem_barSub hV hMN (m : MulAut (Vtil V₀ V hV)) m.2
      (n : MulAut (Vtil V₀ V hV)) hn

theorem barSub_pCoreOf_eq_bot_of_hyp125 {D : Data G} {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) :
    barSub V₀ V h.isElemAbelian (pCoreOf 2 D.M) = ⊥ := by
  by_cases hV₀ : V₀ = ⊥
  · subst hV₀
    have hred : TwoReduced D.M V := by
      rcases h.1 with ⟨hW, -⟩ | ⟨h0, -⟩
      · exact hW.1.2.2
      · exact absurd rfl h0.1.1
    have hcent := TwelveTwentyThree.pCoreOf_le_centralizer_of_twoReduced
      h.pairFacts.le_normalizer hred
    rw [TwelveTwentyThree.barSub_bot_eq_map_autI,
      show autI h.isElemAbelian (pCoreOf 2 D.M) = ⊥ from
        (autI_eq_bot_iff h.isElemAbelian
          ((CFSG.LieType.BorelTits.pCoreOf_le 2 D.M).trans h.pairFacts.le_normalizer)).2 hcent,
      Subgroup.map_bot]
  · obtain ⟨hne, hirr⟩ := TwelveTwentyThree.ne_and_conjGenerated_of_hyp125 h hV₀
    exact TwelveTwentyThree.barSub_pCoreOf_eq_bot h.isElemAbelian h.pairFacts.le hne
      h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀ hirr

theorem barSub_sup_pCoreOf_eq_of_hyp125 {D : Data G} {V₀ V X : Subgroup G} (h : Hyp125 D V₀ V)
    (hX : X ≤ D.M) :
    barSub V₀ V h.isElemAbelian (X ⊔ pCoreOf 2 D.M) = barSub V₀ V h.isElemAbelian X := by
  have hMst : D.M ≤ stabTil V₀ V := le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀
  rw [show barSub V₀ V h.isElemAbelian (X ⊔ pCoreOf 2 D.M) =
      barSub V₀ V h.isElemAbelian X ⊔ barSub V₀ V h.isElemAbelian (pCoreOf 2 D.M) by
    unfold barSub
    rw [Subgroup.subgroupOf_sup (hX.trans hMst)
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 D.M).trans hMst), Subgroup.map_sup],
    barSub_pCoreOf_eq_bot_of_hyp125 h, sup_bot_eq]

theorem barSub_mem_compBar_of_ne_bot {D : Data G} {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hL1 : barSub V₀ V h.isElemAbelian L ≠ ⊥) :
    barSub V₀ V h.isElemAbelian L ∈ compBar D.M V₀ V h.isElemAbelian := by
  have hp := h.pairFacts
  have hLM : L ≤ D.M := hL.1.le
  refine ⟨barSub_mono V₀ V h.isElemAbelian hLM, ?_, ?_⟩
  · exact TwelveTwentyThree.isSubnormal_barSub h.isElemAbelian hL.1
  · exact TwelveTwentyThree.isQuasisimple_barSub h.isElemAbelian
      (hLM.trans (le_stabTil hp.le_normalizer hp.le_normalizer₀)) hL.2.2
      (TwelveTwentyThree.barSub_pCoreOf_eq_bot_of_isSubnormal h.isElemAbelian hL.1
        (barSub_pCoreOf_eq_bot_of_hyp125 h)) hL1

omit [Finite G] in
theorem ne_bot_of_mem_compBar {M V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    {K : Subgroup (MulAut (Vtil V₀ V hV))} (hK : K ∈ compBar M V₀ V hV) : K ≠ ⊥ :=
  TwelveTwentyFour.ne_bot_of_isComponentOf hK

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
