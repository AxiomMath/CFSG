module

public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJNotLeDefs
public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJNotLeRead
public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJNotLeO2
public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJ
public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJYFactsOpen
public import CFSG.RankThree.PartTwo.Sec15.Gagen155Y1Omega
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1T114B
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1T112

public section

namespace CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJ

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec15

variable {G : Type} [Group G] [Finite G]

theorem hj_pCore_eq_bot_of_res1 (hfix : J2AutFixNine) (hE25 : J2HasE25) (h415 : Sec4.Item4_15)
    {A L : Subgroup G} {c : G} (hS : Sec14Std G A c L) (h142 : Concl142 A (lB A))
    (hθ : aschbacherSolvableCore 3 ↥L = CFSG.pCore 2 ↥L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {X K Y M T : Subgroup G} (hC : Ctx155 A X K Y M T)
    {Yc : Subgroup (Res1Q A L)} (hY : Res1AtOf A c L M Yc) (hsimple : IsSimpleGroup ↥Yc)
    (hYF : Res1HJYFacts ↥Yc) :
    CFSG.pCore 2 ↥L = ⊥ ∧ aschbacherSolvableCore 3 ↥L = ⊥ := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨c', hc', -, hcA, hc3, -, hhyp, hAeq⟩ := hj_exists_res1C_lift hS hY
  obtain ⟨U, -, hcU, -⟩ := hj_exists_sylow_two_normalized hS h142 hY hsimple hYF hC c' hc' hcA
  obtain ⟨-, hyYc, hy3⟩ := hj_orderOf_mk_eq_three hY c' hc' hc3
  have hyU := hj_mem_normalizer_sylow U c' hcU hyYc
  obtain ⟨t', -, ht'5, htc⟩ := hj_exists_five_commute hYF U c' hyYc hy3 hyU
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h5, hθ0⟩ :=
    hj_exists_five_lift hfix hE25 h415 hS hθ hJ hAeq c' hc' hhyp t' ht'5 htc
  exact ⟨h5, hθ0⟩

theorem pCoreOf_two_eq_bot_of_pCore {L : Subgroup G} (h : CFSG.pCore 2 ↥L = ⊥) :
    CFSG.Open.pCoreOf 2 L = ⊥ := by
  change (CFSG.pCore 2 ↥L).map L.subtype = ⊥
  rw [h, Subgroup.map_bot]

theorem hj_pCoreOf_le_of_ctx155 (h154 : Item154R) (h415 : Sec4.Item4_15)
    {A L : Subgroup G} {c : G} (hR : Sec15R G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hΩ : omegaA A = {Subgroup.zpowers c}) (hO2L : CFSG.Open.pCoreOf 2 L = ⊥)
    {X K Y M T : Subgroup G} (hC : Ctx155 A X K Y M T) (hKJ : IsJ2Type K) (hLX : ¬ L ≤ X) :
    CFSG.Open.pCoreOf 2 X ≤ CFSG.Open.pCoreOf 2 K := by
  rcases hC.hyp with hω | hKX
  · rcases hω with ⟨-, hA5⟩ | ⟨c', L', hc', hL', hfac⟩
    · exact hj_pCoreOf_le_of_item154 h154 h415 hR hC.mem_k.prop (hC.res ▸ hC.isY.2.1)
        hC.le_k hKJ hA5
    · exfalso
      have hc'c : Subgroup.zpowers c' = Subgroup.zpowers c := by
        rw [hΩ] at hc'
        exact hc'
      have h3L : 3 ∣ Nat.card L := by
        obtain ⟨φ⟩ := hJ
        exact Proof1515.three_dvd_card_of_mulEquiv φ (by rw [KFacts.KS14.card_nativeJ2]; norm_num)
      have hL'L : L' = L := Proof1515.eq_of_mem_lA_of_zpowers_eq hR.toSec14Std h3L hc'c hL'
      subst hL'L
      apply hLX
      rw [hfac, hO2L, sup_bot_eq]
      exact inf_le_right
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact Sylow155R1.pCoreOf_le_pCoreOf_of_le_sup hC.le_k hKX.le

theorem res1L112InPtJ2K_j2_of (hfix : J2AutFixNine) (hE25 : J2HasE25) (h415 : Sec4.Item4_15)
    (h134 : Item134) (h48 : Sec4.Item4_8) (h148 : Item148R) (h142 : Item142R)
    (h142c : Concl142S14) (hθS : HJThetaS14) (hHJ : Step142LowerGenHJ) (h154 : Item154R) :
    Res1L112InPtJ2K Res1J2Pt Res1OpenType := by
  intro G _ _ A c L hR hPt hN hS X K Y M T P' hC hmax habove hE h146 hRP hIX Yc hY hsimple hP
    hEA hEO hcomm hfield hKJ hLX
  have hJ := hPt.2
  have hΩ := Gagen155Y1.omegaA_eq_singleton_of_j2_of_ncard_lt h134 h48 hR hJ hPt.1
  have hθ := hθS G A c L hS hJ
  have h142' : Concl142 A (lB A) := h142c G A c L hS
  have hO2L := pCoreOf_two_eq_bot_of_pCore (hj_pCore_eq_bot_of_res1 hfix hE25 h415 hS h142' hθ
    hJ hC hY hsimple (res1HJYFacts_of_res1OpenType hP)).1
  obtain ⟨hKL, hLK⟩ := hj_eq_inf_sup_of_j2Type h148 h134 h48 h142 hR hJ hθ hΩ
    hC.mem_k.prop.1 hKJ
  have hLK' : L ≤ K := by
    rw [hLK, hO2L, sup_bot_eq]
    exact inf_le_right
  refine ⟨Sylow155R1.le_delta_of_j2 hHJ hR h142' hJ, hLK', ?_,
    hj_pCoreOf_le_of_ctx155 h154 h415 hR hJ hΩ hO2L hC hKJ hLX⟩
  rw [inf_eq_right.mpr hLK'] at hKL
  exact hKL

theorem res1L112InPt_j2_of_j2K (h134 : Item134) (h48 : Sec4.Item4_8) (h148 : Item148R)
    (h142 : Item142R) (hθS : HJThetaS14) (hK : Res1L112InPtJ2K Res1J2Pt Res1OpenType)
    (h156 : Res1J2Item156) (hX1 : Res1J2X1) :
    Sylow155R1.Res1L112InPt Res1J2Pt Res1OpenType := by
  intro G _ _ A c L hR hPt hN hS X K Y M T P' hC hmax habove hE h146 hRP hIX Yc hY hsimple hP
    hEA hEO hcomm hfield hLX
  have hJ := hPt.2
  have hΩ := Gagen155Y1.omegaA_eq_singleton_of_j2_of_ncard_lt h134 h48 hR hJ hPt.1
  rcases hj_read148_of_omegaA_eq h148 h134 h48 h142 hR hJ (hθS G A c L hS hJ) hΩ
      hC.mem_k.prop.1 with ht | h7 | h37 | ⟨hKJ, -⟩
  · exfalso
    obtain ⟨h5, h6, hON⟩ := h156 G A c L hR hJ hΩ K hC.mem_k
    rcases ht with he | h6' | hON'
    · exact h5.false he.some
    · exact h6 h6'
    · exact hON hON'
  · exact ((hX1 G A c L hR hJ hΩ K hC.mem_k).1.false h7.some).elim
  · exact ((hX1 G A c L hR hJ hΩ K hC.mem_k).2 h37).elim
  · exact hK G A c L hR hPt hN hS X K Y M T P' hC hmax habove hE h146 hRP hIX Yc hY hsimple hP
      hEA hEO hcomm hfield hKJ hLX

end CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJ
