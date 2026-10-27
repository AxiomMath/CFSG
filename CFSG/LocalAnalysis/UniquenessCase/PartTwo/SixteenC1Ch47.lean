module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Ch47Card
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Ch47Cases
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Ch47Pick
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSetupB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem r16_47ch_of (D : Data G) (h45 : R16_45 D) (h45b : R16_45b D) (h46 : R16_46 D)
    (hO1 : R16_47_O1_ne D) (hcard : R16_47_card_le D) (hord : R16_47_ord_gap D) :
    R16_47ch D := by
  intro V₀ V L hV hS hc hL hU4
  obtain ⟨x, hx, hch⟩ := s16c1_exists_pick D h45 hO1 hS hc hL hU4
  have hP := hS.setting.hyp151.hyp125.pairFacts
  have hVc : InCalV D.M V := hyp123_inCalV hS.setting.hyp151.hyp125.1
  have hSyl : IsSylowIn 2 (D.T ⊓ centralizer ({x.val} : Set G)) (centralizer ({x.val} : Set G)) :=
    (h45b V₀ V L hV hS hc x hx).2.1
  have h46' : Concl1646 L x.val := h46 V₀ V L hV hS hc hL hU4 x hx
  have hle : Nat.card ↥V ≤ 2 * Nat.card ↥(uOne V x.val) :=
    hcard V₀ V L hV hS hc hL hU4 x hx hch hSyl h46'
  obtain ⟨g, hg, hz⟩ := hch
  obtain ⟨hcard2, hstar⟩ := s16c1_card_eq_two_mul_uOne hVc hg hz hle
  refine ⟨x, hx, ⟨hstar, ?_⟩, ⟨g, hg, hz⟩⟩
  exact s16c1_orders_of_cases hV x.val_mem
    (s16c1_cases_of_gaps D h45 hord hS hc hL hU4 hx ⟨g, hg, hz⟩ hSyl h46' hcard2)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
