module

public import CFSG.LocalAnalysis.OddStandard.RouteWStdEleven
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenL44
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Section5Hered
public import CFSG.LocalAnalysis.EvenSporadicStandard.Frontier.Child7

public section

namespace CFSG.Yardstones.M0362f3a873a3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.OddStandard
open CFSG.OddStandard.AltStdSec CFSG.OddStandard.AltStdBal

theorem false_of_stdHyp_hs_ten_of_hsSection5
    {G : Type} [Group G] [Finite G]
    (h5 : CFSG.EvenSporadicStandard.HSStd.HSSection5At G)
    (h7 : CFSG.EvenSporadicStandard.TwoHSGivesHN)
    {L Q : Subgroup G} {z u : G}
    (h : Setting G L 10) (d : Cyc L Q z) (T : ShapeTwo L Q z u) {K : Subgroup G}
    (hK : CFSG.EvenSporadicStandard.StdHyp G K) (hq : IsSporadic (K ⧸ center K) .HS) : False := by
  have hqs := hK.standard.1
  by_cases hZ : center K = ⊥
  · obtain ⟨φ⟩ := hq
    exact CFSG.EvenSporadicStandard.HSStd.hs_not_standard_of_section5At h5 hK
      ⟨(QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans φ⟩
  · have hperf : Group.IsPerfect K := ⟨hqs.1⟩
    have h2 : Nat.card (center K) = 2 :=
      CFSG.EvenSporadicStandard.HSStd.Zassenhaus.card_center_eq_two_of_ne_bot hperf hq hZ
    obtain ⟨φ⟩ := h7 G K hK h2 hq
    obtain ⟨e⟩ := h.iso
    have hCz := card_centralizer_eq_two_mul_factorial h d T.card T.cent T.outer T.sq e
    rw [card_centralizer_mulEquiv φ z] at hCz
    have hord : orderOf (φ z) = 2 := by rw [MulEquiv.orderOf_eq]; exact d.order
    exact hn_card_centralizer_ne (φ z) hord hCz

theorem shapeTwoSmallTen_of_yardstones
    (h9 : ShapeTwoSmallNine) (hHS : ShapeTwoTenStdHS)
    (h5 : CFSG.EvenSporadicStandard.HSStd.HSSection5)
    (h7 : CFSG.EvenSporadicStandard.TwoHSGivesHN) : ShapeTwoSmallTen := by
  intro G _ _ L Q n z u h d T hn
  rcases Nat.lt_or_ge n 10 with h10 | h10
  · exact h9 G L Q n z u h d T (by omega)
  · obtain rfl : n = 10 := by omega
    obtain ⟨K, hK, hq⟩ := hHS G L Q z u h d T
    exact false_of_stdHyp_hs_ten_of_hsSection5 (h5 G) h7 h d T hK hq

theorem altStdCyclicBalancedFalse_of_yardstones
    (y01 : AltStdBalancedOrder2InnerSmall) (y02 : ShapeTwoSmallNine)
    (y03 : ShapeTwoTenNoSwapPartnerNoCentralStdHS) (y04 : ShapeTwoTenSwapPartnerStdHS)
    (y05 : CFSG.EvenSporadicStandard.HSStd.HSSection5)
    (y06 : CFSG.EvenSporadicStandard.TwoHS.HaradaHNRecognitionKP)
    (y07 : CFSG.EvenSporadicStandard.TwoHS.GH312Fixed) : AltStdCyclicBalancedFalse :=
  altStdCyclicBalancedFalse_of_small_eleven y01
    (shapeTwoSmallEleven_of_ten_holds (shapeTwoSmallTen_of_yardstones y02
      (shapeTwoTenStdHS_of_parts' CFSG.SeitzReduction.gls3OddLieAutComponentsInput
        CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput shapeTwoTenL44Excl_holds
        y03 y04)
      y05 (CFSG.EvenSporadicStandard.Frontier.child7_of_frontier y06 y07)))
    shapeTwoCentDoubleAt_twelve_holds

end CFSG.Yardstones.M0362f3a873a3
