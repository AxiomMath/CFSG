module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenElevenSp4Setup
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenElevenLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TwoNatHolds
public import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport
public import CFSG.Quasithin.Background.E3AParamCard

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin (IsSylowIn)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.ComponentClassification.CatLeafProof
  (lieModel_eq_of_isChar2LieShape fieldExponent_eq_of_isChar2LieShape)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

section Certified


theorem gap_18_11_W_of (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (h1742 : S17.R17_42At D V₀ V)
    (h6b : R18_6bAt D V₀ V p L h) (h7b : R18_7bAt D V₀ V p L h)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3)
    (h8 : R18_8At D V₀ V p L h) (h9 : R18_9At D V₀ V p L h) (h10 : R18_10At D V₀ V p L h)
    (hKns : K_Sp4TwoNat_noSwap) (hSg : UC6S846.SigmaStd D) (h638 : UC6.R6_38 D)
    (h72 : F07.R72 D) (hK35 : UCK.K35w) (h109 : Inputs1719.UC2_10_9 D)
    (h111 : W3Thm111 G)
    (hKI : Inputs1719.K_Sp4TwoNat_involution) :
    Gap_18_11_W D V₀ V p L h := by
  rintro ⟨n, hSp⟩ hV₀
  subst hV₀
  classical
  obtain ⟨hV, hV₀el, hV₀le, hVM, hMnorm, hMnorm₀, hVne⟩ := h.hyp125.pairFacts
  have hm3 : MBarGT D.M ⊥ V 3 := h1669 (by rw [Subgroup.card_bot]; norm_num)
  have hSpBar2 : IsSp4 (Bar2 (conjClosure D.M L)) n := isSp4_bar2_of_isSp4_barSub h hSp
  obtain ⟨hXL, -, hn1, hodd, hcong, -, hmore⟩ :=
    isSp4_or_isG2_bar2_cong_more h h1742 (Or.inl hSpBar2)
  have hXc : conjClosure D.M L ∈ calC D.M := by rw [hXL]; exact h.hL.1
  have hXM : conjClosure D.M L ≤ D.M := TwelveTwentyThree.conjClosure_le h.hL.1.1.le
  have hMstab : D.M ≤ stabTil ⊥ V := le_stabTil hMnorm hMnorm₀
  have hXstab : conjClosure D.M L ≤ stabTil ⊥ V := hXM.trans hMstab
  have hXn : ((conjClosure D.M L).subgroupOf D.M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXM).mpr
      (TwelveTwentyThree.le_normalizer_conjClosure D.M L)
  have hTsyl : IsSylowIn 2 D.T D.M := CFSG.ABGLocalTools.isSylowOf_iff.mp D.sylowM
  have hTL : D.T ≤ Subgroup.normalizer (conjClosure D.M L : Set G) :=
    D.sylowM.le.trans (TwelveTwentyThree.le_normalizer_conjClosure D.M L)
  have hXsub : CFSG.Open.IsSubnormal (conjClosure D.M L) D.M :=
    CFSG.Open.IsSubnormal.step hXM hXn (CFSG.Open.IsSubnormal.refl D.M)
  have hsimple : IsSimpleGroup (Bar2 (conjClosure D.M L)) :=
    (uc22p22a_sp4_simple _ n hSpBar2).1
  have hX1 : barSub ⊥ V hV (conjClosure D.M L) ≠ ⊥ := by
    have hs : IsSimpleGroup ↥(barSub ⊥ V hV (conjClosure D.M L)) :=
      LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hSp
    exact (Subgroup.nontrivial_iff_ne_bot _).mp hs.toNontrivial
  have hns : ¬ S17.SwapsParabolics D.T (conjClosure D.M L) :=
    not_swapsParabolics_of_isSp4_df D h hm3 h6b h7b h8 h9 h10 hSp hKns
  obtain ⟨⟨r, hr, hr7, hrdvd, hXr, hrankE⟩, hpX, hn3, hcong', hpn, hZ, hOut⟩ :=
    sp4_rootLine_setup D h h1742 hSp
  have hr2 : r ≠ 2 := by omega
  have hWsq : ∀ w : Vtil ⊥ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one ⊥ V hV
  have hSpData : Sp4TwoNatData (barSub ⊥ V hV (conjClosure D.M L)) n := by
    obtain ⟨-, K, hKf, hKfin, π, hKcard, hsum⟩ :=
      sp4Data_of_df D h hm3 h6b h7b h8 h9 h10 hSp
    exact ⟨hSp, K, hKf, hKfin, π, hKcard, hsum⟩
  have hSylS : IsSylowIn 2 (barSub ⊥ V hV D.T ⊓ barSub ⊥ V hV (conjClosure D.M L))
      (barSub ⊥ V hV (conjClosure D.M L)) :=
    EighteenElevenTransport.barSub_inf_isSylow hV hMstab hTsyl hXM hXn
  obtain ⟨P, Q, hPH, hSP, hQS, hPQ, hidx, hfixKW, b₂, hb₂P, x₂, hx₂P, Y₂,
    hb₂S, hord₂, hconj₂, hY₂, hL2Y₂⟩ :=
    k_Sp4TwoNat_lineParabolic_holds (Vtil ⊥ V hV) hWsq (barSub ⊥ V hV (conjClosure D.M L))
      (barSub ⊥ V hV D.T ⊓ barSub ⊥ V hV (conjClosure D.M L)) n r hSpData hSylS hr hrdvd
  let P2 : Subgroup G := preBarSub (conjClosure D.M L) ⊥ V hV P
  let X2 : Subgroup G := D.T ⊔ P2
  have hP2X : P2 ≤ conjClosure D.M L := by
    intro x hx
    exact ((mem_preBarSub (conjClosure D.M L) ⊥ V hV P).1 hx).1
  have hP2M : P2 ≤ D.M := hP2X.trans hXM
  have hP2X2 : P2 ≤ X2 := le_sup_right
  have hTP2 : D.T ≤ Subgroup.normalizer (P2 : Set G) := by
    have hSPN : barSub ⊥ V hV D.T ⊓ barSub ⊥ V hV (conjClosure D.M L) ≤
        Subgroup.normalizer (P : Set (MulAut (Vtil ⊥ V hV))) :=
      hSP.trans (Subgroup.le_normalizer)
    rw [EighteenElevenTransport.barSub_inf_eq hV hMstab hTsyl hXM hXn] at hSPN
    exact le_normalizer_preBarSub_of_centOverO2 D h hXc hTL hns hodd hSpBar2 hZ hPH hSPN
  have hX2M : X2 ≤ D.M := sup_le D.sylowM.le hP2M
  have hS : IsSylowIn 2 D.T X2 := TwelveShort.isSylowIn_of_le D le_sup_left
  have hF : CFSG.QuasithinUnique.CharTwo X2 :=
    CFSG.QuasithinUnique.CharTwo.of_pCoreOf_le (D.standing.charTwo D.M D.maxLocal.1) hX2M
      ((CFSG.Quasithin.E1.pCoreOf_two_le_of_isSylowIn hTsyl).trans le_sup_left)
  have hX2N : X2 ≤ Subgroup.normalizer (P2 : Set G) :=
    sup_le hTP2 (Subgroup.le_normalizer)
  have hP2norm : (P2.subgroupOf X2).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hX2N
  have hodd_mem : ∀ g ∈ X2, Odd (orderOf g) → g ∈ P2 := by
    intro g hgX2 hgodd
    have hg : g ∈ (D.T : Set G) * (P2 : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right D.T P2 hTP2]
      exact hgX2
    obtain ⟨t, ht, pp, hp, rfl⟩ := hg
    have htX2 : t ∈ X2 := Subgroup.mem_sup_left ht
    have hpX2 : pp ∈ X2 := Subgroup.mem_sup_right hp
    have hq : QuotientGroup.mk' (P2.subgroupOf X2) ⟨t * pp, hgX2⟩ =
        QuotientGroup.mk' (P2.subgroupOf X2) ⟨t, htX2⟩ := by
      rw [show (⟨t * pp, hgX2⟩ : ↥X2) = ⟨t, htX2⟩ * ⟨pp, hpX2⟩ from rfl, map_mul]
      have hq1 : QuotientGroup.mk' (P2.subgroupOf X2) ⟨pp, hpX2⟩ = 1 := by
        simp only [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact Subgroup.mem_subgroupOf.mpr hp
      rw [hq1, mul_one]
    have hdvd1 : orderOf (QuotientGroup.mk' (P2.subgroupOf X2) ⟨t * pp, hgX2⟩) ∣
        orderOf (⟨t, htX2⟩ : ↥X2) := by
      rw [hq]
      exact orderOf_map_dvd (QuotientGroup.mk' (P2.subgroupOf X2)) ⟨t, htX2⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf).mp D.sylowM.isPGroup ⟨t, ht⟩
    have htk : orderOf (⟨t, htX2⟩ : ↥X2) = 2 ^ k := by
      rw [← Subgroup.orderOf_coe ⟨t, htX2⟩]
      exact (Subgroup.orderOf_coe ⟨t, ht⟩).trans hk
    have hdvd2 : orderOf (QuotientGroup.mk' (P2.subgroupOf X2) ⟨t * pp, hgX2⟩) ∣ 2 ^ k :=
      htk ▸ hdvd1
    obtain ⟨j, hjk, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd2
    have hoddq : Odd (orderOf (QuotientGroup.mk' (P2.subgroupOf X2) ⟨t * pp, hgX2⟩)) := by
      refine Odd.of_dvd_nat ?_ (orderOf_map_dvd (QuotientGroup.mk' (P2.subgroupOf X2))
        ⟨t * pp, hgX2⟩)
      exact Subgroup.orderOf_coe (⟨t * pp, hgX2⟩ : ↥X2) ▸ hgodd
    have hj0 : j = 0 := by
      rcases Nat.eq_zero_or_pos j with h | h
      · exact h
      · exfalso
        have h2 : 2 ∣ 2 ^ j := dvd_pow_self 2 h.ne'
        rw [hj] at hoddq
        exact (Nat.not_even_iff_odd.mpr hoddq) (even_iff_two_dvd.mpr h2)
    have hq1 : QuotientGroup.mk' (P2.subgroupOf X2) ⟨t * pp, hgX2⟩ = 1 := by
      apply orderOf_eq_one_iff.mp
      rw [hj, hj0, pow_zero]
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hq1
    exact Subgroup.mem_subgroupOf.mp hq1
  let U0 : Subgroup G := V ⊓ CFSG.Quasithin.centerOf D.T
  have hVT : V ≤ D.T := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22na_le_T_of_inCalV D
    (hyp123_inCalV h.hyp125.1)
  have hTV : D.T ≤ Subgroup.normalizer (V : Set G) := D.sylowM.le.trans hMnorm
  have hU0ne : U0 ≠ ⊥ := uc22p22na_inf_center_ne_bot D.sylowM.isPGroup hVT hTV hVne
  have hU0T : U0 ≤ Subgroup.centralizer (D.T : Set G) := by
    intro u hu
    exact Subgroup.mem_centralizer_iff.mpr fun t ht =>
      Subgroup.mem_centralizer_iff.mp hu.2.2 t ht
  have hTU0 : D.T ≤ Subgroup.centralizer (U0 : Set G) := by
    intro t ht
    exact Subgroup.mem_centralizer_iff.mpr fun u hu =>
      (Subgroup.mem_centralizer_iff.mp (hU0T hu) t ht).symm

  have hO2le : pCoreOf 2 (conjClosure D.M L) ≤ D.T ⊓ conjClosure D.M L := by
    have hO2normal : ((pCoreOf 2 (conjClosure D.M L)).subgroupOf
        (conjClosure D.M L)).Normal := by
      rw [Subgroup.normal_subgroupOf_iff (CFSG.LieType.BorelTits.pCoreOf_le 2 _)]
      intro a b ha hb
      exact CFSG.ClassicalGroups.PCoreSection.conj_mem_pCoreOf hb ha
    have hSylIn : IsSylowIn 2 (D.T ⊓ conjClosure D.M L) (conjClosure D.M L) :=
      (CFSG.ABGLocalTools.isSylowOf_iff (p := 2) (P := D.T ⊓ conjClosure D.M L)
        (K := conjClosure D.M L)).mp
        (CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer D.sylowM hXM
          (TwelveTwentyThree.le_normalizer_conjClosure D.M L))
    exact hSylIn.le_of_normal (CFSG.LieType.BorelTits.pCoreOf_le 2 _) hO2normal
      (CFSG.ClassicalGroups.PCoreSection.isPGroup_pCoreOf 2 _)
  have hodd_one : ∀ y ∈ X2 ⊓ Subgroup.centralizer (U0 : Set G), Odd (orderOf y) → y = 1 := by
    intro y hy hyodd
    have hyX2 : y ∈ X2 := hy.1
    have hyC : y ∈ Subgroup.centralizer (U0 : Set G) := hy.2
    have hyP2 : y ∈ P2 := hodd_mem y hyX2 hyodd
    have hys : y ∈ stabTil ⊥ V := hXstab (hP2X hyP2)
    have hactP : actTil ⊥ V hV ⟨y, hys⟩ ∈ P :=
      ((mem_preBarSub (conjClosure D.M L) ⊥ V hV P).1 hyP2).2.2
    obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU0ne
    have huU0 : (u : G) ∈ U0 := u.2
    have huV : (u : G) ∈ V := u.2.1
    have hfixu : actTil ⊥ V hV ⟨y, hys⟩ (tilOf ⊥ V hV (u : G) huV) =
        tilOf ⊥ V hV (u : G) huV := by
      have hyu : y * (u : G) * y⁻¹ = (u : G) := by
        have hcomm := Subgroup.mem_centralizer_iff.mp hyC (u : G) huU0
        calc y * (u : G) * y⁻¹ = (u : G) * y * y⁻¹ := by rw [hcomm]
          _ = (u : G) := by group
      rw [tilOf, actTil_mk, mkTil_eq_iff, actStab_apply_val]
      change y * (u : G) * y⁻¹ * (u : G)⁻¹ ∈ (⊥ : Subgroup G)
      rw [hyu, mul_inv_cancel]
      exact Subgroup.mem_bot.mpr rfl
    have hoddact : Odd (orderOf (actTil ⊥ V hV ⟨y, hys⟩)) := by
      refine Odd.of_dvd_nat ?_ (orderOf_map_dvd (actTil ⊥ V hV) ⟨y, hys⟩)
      exact Subgroup.orderOf_coe ⟨y, hys⟩ ▸ hyodd
    have hfixS : tilOf ⊥ V hV (u : G) huV ∈
        CFSG.Quasithin.fixV (barSub ⊥ V hV D.T ⊓ barSub ⊥ V hV (conjClosure D.M L)) := by
      refine CFSG.Quasithin.mem_fixV.mpr fun x hx => ?_
      obtain ⟨s, hss, hxs⟩ := (mem_barSub ⊥ V hV D.T x).1 hx.1
      rw [← hxs, tilOf, actTil_mk, mkTil_eq_iff, actStab_apply_val]
      change (s : G) * (u : G) * (s : G)⁻¹ * (u : G)⁻¹ ∈ (⊥ : Subgroup G)
      have hsu : (s : G) * (u : G) * (s : G)⁻¹ = (u : G) := by
        have hcomm := Subgroup.mem_centralizer_iff.mp (hU0T huU0) (s : G) hss
        calc (s : G) * (u : G) * (s : G)⁻¹ = (u : G) * (s : G) * (s : G)⁻¹ := by rw [hcomm]
          _ = (u : G) := by group
      rw [hsu, mul_inv_cancel]
      exact Subgroup.mem_bot.mpr rfl
    have hu_til_ne : tilOf ⊥ V hV (u : G) huV ≠ 1 := by
      intro h
      have h1 : (u : G) ∈ (⊥ : Subgroup G) := by
        rw [tilOf, mkTil, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_modNull] at h
        exact h
      exact hu1 (Subtype.ext (Subgroup.mem_bot.mp h1))
    have hone : actTil ⊥ V hV ⟨y, hys⟩ = 1 :=
      hfixKW _ hfixS hu_til_ne _ hactP hoddact hfixu
    have hyO2 : y ∈ pCoreOf 2 (conjClosure D.M L) :=
      mem_pCoreOf_of_actTil_eq_one h.hyp125 hXsub hsimple hX1 (hP2X hyP2) hys hone
    have hyT : y ∈ D.T := (hO2le hyO2).1
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf).mp D.sylowM.isPGroup ⟨y, hyT⟩
    have hyk : orderOf y = 2 ^ k := (Subgroup.orderOf_coe ⟨y, hyT⟩).trans hk
    rw [hyk] at hyodd
    have hk0 : k = 0 := by
      by_contra hk0
      exact (Nat.not_even_iff_odd.mpr hyodd) (Nat.even_pow.mpr ⟨even_two, hk0⟩)
    rw [hk0, pow_zero] at hyk
    exact orderOf_eq_one_iff.mp hyk
  have hH2 : IsPGroup 2 ↥(X2 ⊓ Subgroup.centralizer (U0 : Set G)) := by
    apply isPGroup_iff_pow_pow_eq_one.mpr
    intro c
    obtain ⟨a, m, hm, hk⟩ := Nat.exists_eq_two_pow_mul_odd (n := orderOf c) (orderOf_pos c).ne'
    have hcdvd : 2 ^ a ∣ orderOf c := ⟨m, hk⟩
    have hord : orderOf (c ^ 2 ^ a) = m := by
      rw [orderOf_pow_of_dvd (pow_ne_zero a two_ne_zero) hcdvd, hk,
        Nat.mul_div_cancel_left m (pow_pos two_pos a)]
    have hc : (c : G) ∈ X2 ⊓ Subgroup.centralizer (U0 : Set G) := c.2
    have hordG : orderOf ((c : G) ^ 2 ^ a) = m := by
      rw [show (c : G) ^ 2 ^ a = ((c ^ 2 ^ a : ↥(X2 ⊓ Subgroup.centralizer (U0 : Set G))) : G)
        from (map_pow (Subgroup.subtype _) c (2 ^ a)).symm,
        Subgroup.orderOf_coe, hord]
    have hpow1 : (c : G) ^ 2 ^ a = 1 :=
      hodd_one _ (Subgroup.pow_mem _ hc _) (by rw [hordG]; exact hm)
    exact ⟨a, Subtype.ext hpow1⟩
  have hT_le_hCU : D.T ≤ X2 ⊓ Subgroup.centralizer (U0 : Set G) := le_inf le_sup_left hTU0
  have hCU : X2 ⊓ Subgroup.centralizer (U0 : Set G) = D.T :=
    CFSG.LargeExtraspecial.S5.IsSylowTwoIn.eq_of_le
      (show CFSG.LargeExtraspecial.S5.IsSylowTwoIn D.T X2 from ⟨hS.1, hS.2.1, hS.2.2⟩)
      hT_le_hCU inf_le_left hH2
  let U : Subgroup G :=
    CFSG.Quasithin.conjClosure (CFSG.Quasithin.omegaOneCenterOf D.T) X2
  have hUel : IsElemAbelian 2 U :=
    CFSG.LocalAnalysis.WeakClosure81.omegaOneCenter_conjClosure_isElemAbelian hF hS
  have hX2U : X2 ≤ Subgroup.normalizer (U : Set G) :=
    CFSG.Quasithin.le_normalizer_conjClosure (CFSG.Quasithin.omegaOneCenterOf D.T) X2
  let Cc : Subgroup G := F08.CentOverO2 D.M (conjClosure D.M L)
  let R' : Subgroup G :=
    (D.T ⊓ Cc) ⊔ preBarSub (conjClosure D.M L) ⊥ V hV Q
  have hpreS : preBarSub (conjClosure D.M L) ⊥ V hV
      (barSub ⊥ V hV D.T ⊓ barSub ⊥ V hV (conjClosure D.M L)) =
      D.T ⊓ conjClosure D.M L := by
    rw [EighteenElevenTransport.barSub_inf_eq hV hMstab hTsyl hXM hXn]
    exact preBarSub_S_eq D h hsimple hX1
  have hE_le_D : preBarSub (conjClosure D.M L) ⊥ V hV Q ≤ D.T ⊓ conjClosure D.M L := by
    intro g hg
    obtain ⟨hgM, hgs, hgQ⟩ := (mem_preBarSub (conjClosure D.M L) ⊥ V hV Q).1 hg
    rw [← hpreS]
    exact (mem_preBarSub (conjClosure D.M L) ⊥ V hV _).2 ⟨hgM, hgs, hQS hgQ⟩
  have hR'T : R' ≤ D.T := sup_le inf_le_left (hE_le_D.trans inf_le_left)
  have hR'X2 : R' ≤ X2 := hR'T.trans le_sup_left
  have hR'2 : IsPGroup 2 ↥R' := D.sylowM.isPGroup.to_le hR'T
  have hMnormal : D.M ≤ Subgroup.normalizer (conjClosure D.M L : Set G) :=
    TwelveTwentyThree.le_normalizer_conjClosure D.M L
  have hMO2 : D.M ≤ Subgroup.normalizer
      (pCoreOf 2 (conjClosure D.M L) : Set G) :=
    hMnormal.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) _)
  have hmemX : ∀ {g u : G}, g ∈ D.M → u ∈ conjClosure D.M L →
      g * u * g⁻¹ ∈ conjClosure D.M L :=
    fun hg hu => (Subgroup.mem_normalizer_iff.mp (hMnormal hg) _).1 hu
  have hmemO2 : ∀ {g o : G}, g ∈ D.M → o ∈ pCoreOf 2 (conjClosure D.M L) →
      g * o * g⁻¹ ∈ pCoreOf 2 (conjClosure D.M L) :=
    fun hg ho => (Subgroup.mem_normalizer_iff.mp (hMO2 hg) _).1 ho
  have hTdecomp : ∀ t ∈ D.T, ∃ s ∈ D.T ⊓ conjClosure D.M L, ∃ c ∈ D.T ⊓ Cc, t = s * c := by
    intro t ht
    obtain ⟨s, hs, hc⟩ := exists_mem_inf_mul_centOverO2 D h hXc hTL hns hodd hSpBar2 hZ t ht
    exact ⟨s, hs, s⁻¹ * t, ⟨D.T.mul_mem (D.T.inv_mem hs.1) ht, hc⟩, by group⟩
  have hCM' : ∀ m ∈ D.M, ∀ y ∈ Cc, m * y * m⁻¹ ∈ Cc := by
    intro m hm y hy
    obtain ⟨hyM, hyc⟩ :=
      (mem_centOverO2_iff (X := D.M) (L := conjClosure D.M L)).1 hy
    refine (mem_centOverO2_iff (X := D.M) (L := conjClosure D.M L)).2 ⟨?_, ?_⟩
    · exact D.M.mul_mem (D.M.mul_mem hm hyM) (D.M.inv_mem hm)
    · intro l hl
      have hmlX : m⁻¹ * l * m ∈ conjClosure D.M L := by
        simpa using hmemX (D.M.inv_mem hm) hl
      have h1 := hyc (m⁻¹ * l * m) hmlX
      have h2 : (m * y * m⁻¹) * l * (m * y * m⁻¹)⁻¹ * l⁻¹ =
          m * (y * (m⁻¹ * l * m) * y⁻¹ * (m⁻¹ * l * m)⁻¹) * m⁻¹ := by group
      rw [h2]
      exact hmemO2 hm h1
  have hCM : D.M ≤ Subgroup.normalizer (Cc : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact hCM' m hm y
    · intro hy
      have h := hCM' m⁻¹ (D.M.inv_mem hm) (m * y * m⁻¹) hy
      rwa [show m⁻¹ * (m * y * m⁻¹) * (m⁻¹)⁻¹ = y from by group] at h
  have hTCN : D.T ≤ Subgroup.normalizer ((D.T ⊓ Cc) : Set G) :=
    (le_inf Subgroup.le_normalizer (D.sylowM.le.trans hCM)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hconjTC : ∀ x ∈ X2, ∀ y ∈ D.T ⊓ Cc, x * y * x⁻¹ ∈ D.T ⊓ Cc := by
    intro x hx y hy
    have hx' : x ∈ (D.T : Set G) * (P2 : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right D.T P2 hTP2]
      exact hx
    obtain ⟨t, ht, p, hp, rfl⟩ := hx'
    have hpX : p ∈ conjClosure D.M L := hP2X hp
    have ho : y * p * y⁻¹ * p⁻¹ ∈ pCoreOf 2 (conjClosure D.M L) :=
      ((mem_centOverO2_iff (X := D.M) (L := conjClosure D.M L)).1 hy.2).2 p hpX
    have hpyT : p * y * p⁻¹ ∈ D.T := by
      have h1 : p * y * p⁻¹ = (y * p * y⁻¹ * p⁻¹)⁻¹ * y := by group
      rw [h1]
      exact D.T.mul_mem (D.T.inv_mem (hO2le ho).1) hy.1
    have hpyC : p * y * p⁻¹ ∈ Cc := hCM' p (hXM hpX) y hy.2
    have htpy : t * (p * y * p⁻¹) * t⁻¹ ∈ D.T ⊓ Cc :=
      (Subgroup.mem_normalizer_iff.mp (hTCN ht) _).1 ⟨hpyT, hpyC⟩
    have heq : (t * p) * y * (t * p)⁻¹ = t * (p * y * p⁻¹) * t⁻¹ := by group
    rw [heq]
    exact htpy
  have hP2pre : P2 ≤ Subgroup.normalizer
      (preBarSub (conjClosure D.M L) ⊥ V hV Q : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro g hg y hy
    obtain ⟨hgM, hgs, hgP⟩ := (mem_preBarSub (conjClosure D.M L) ⊥ V hV P).1 hg
    obtain ⟨hyM, hys, hyQ⟩ := (mem_preBarSub (conjClosure D.M L) ⊥ V hV Q).1 hy
    have hconjS : g * y * g⁻¹ ∈ stabTil ⊥ V :=
      (stabTil ⊥ V).mul_mem ((stabTil ⊥ V).mul_mem hgs hys) ((stabTil ⊥ V).inv_mem hgs)
    refine (mem_preBarSub (conjClosure D.M L) ⊥ V hV Q).2 ⟨?_, hconjS, ?_⟩
    · exact (conjClosure D.M L).mul_mem
        ((conjClosure D.M L).mul_mem (hP2X hg) hyM)
        ((conjClosure D.M L).inv_mem (hP2X hg))
    · have hsub : (⟨g * y * g⁻¹, hconjS⟩ : ↥(stabTil ⊥ V)) =
          ⟨g, hgs⟩ * ⟨y, hys⟩ * ⟨g, hgs⟩⁻¹ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk]
      have e : actTil ⊥ V hV ⟨g * y * g⁻¹, hconjS⟩ =
          actTil ⊥ V hV ⟨g, hgs⟩ * actTil ⊥ V hV ⟨y, hys⟩ *
            (actTil ⊥ V hV ⟨g, hgs⟩)⁻¹ := by
        rw [hsub]
        simp only [map_mul, map_inv]
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (hPQ hgP) _).1 hyQ
  have hTpre : D.T ≤ Subgroup.normalizer
      (preBarSub (conjClosure D.M L) ⊥ V hV Q : Set G) := by
    have hQX : Q ≤ barSub ⊥ V hV (conjClosure D.M L) := hQS.trans inf_le_right
    have hspN : barSub ⊥ V hV (D.T ⊓ conjClosure D.M L) ≤
        Subgroup.normalizer (Q : Set (MulAut (Vtil ⊥ V hV))) := by
      rw [← EighteenElevenTransport.barSub_inf_eq hV hMstab hTsyl hXM hXn]
      exact hSP.trans hPQ
    exact le_normalizer_preBarSub_of_centOverO2 D h hXc hTL hns hodd hSpBar2 hZ hQX hspN
  have hconjPre : ∀ x ∈ X2, ∀ y ∈ preBarSub (conjClosure D.M L) ⊥ V hV Q,
      x * y * x⁻¹ ∈ preBarSub (conjClosure D.M L) ⊥ V hV Q := by
    intro x hx y hy
    have hx' : x ∈ (D.T : Set G) * (P2 : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right D.T P2 hTP2]
      exact hx
    obtain ⟨t, ht, p, hp, rfl⟩ := hx'
    have h1 : p * y * p⁻¹ ∈ preBarSub (conjClosure D.M L) ⊥ V hV Q :=
      (Subgroup.le_normalizer_iff.mp hP2pre) p hp y hy
    have h2 : t * (p * y * p⁻¹) * t⁻¹ ∈ preBarSub (conjClosure D.M L) ⊥ V hV Q :=
      (Subgroup.le_normalizer_iff.mp hTpre) t ht _ h1
    have heq : (t * p) * y * (t * p)⁻¹ = t * (p * y * p⁻¹) * t⁻¹ := by group
    rw [heq]
    exact h2
  have hX2R' : X2 ≤ Subgroup.normalizer (R' : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rw [show R' = (D.T ⊓ Cc) ⊔
      preBarSub (conjClosure D.M L) ⊥ V hV Q from rfl, Subgroup.map_sup]
    congr 1
    · refine le_antisymm ?_ ?_
      · intro z hz
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hz
        exact hconjTC x hx y hy
      · intro z hz
        refine Subgroup.mem_map.2 ⟨x⁻¹ * z * x, ?_, ?_⟩
        · have h := hconjTC x⁻¹ (X2.inv_mem hx) z hz
          simpa using h
        · show x * (x⁻¹ * z * x) * x⁻¹ = z
          group
    · refine le_antisymm ?_ ?_
      · intro z hz
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hz
        exact hconjPre x hx y hy
      · intro z hz
        refine Subgroup.mem_map.2 ⟨x⁻¹ * z * x, ?_, ?_⟩
        · have h := hconjPre x⁻¹ (X2.inv_mem hx) z hz
          simpa using h
        · show x * (x⁻¹ * z * x) * x⁻¹ = z
          group
  have hR'norm : (R'.subgroupOf X2).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hX2R'

  have hR'Z : ∀ r ∈ R', ∀ z ∈ CFSG.Quasithin.omegaOneCenterOf D.T, r * z = z * r := by
    intro r hr z hz
    have hzC : z ∈ Subgroup.centralizer (D.T : Set G) := by
      have hz1 : z ∈ CFSG.Quasithin.centerOf D.T := by
        have hmem := hz
        rw [CFSG.Quasithin.omegaOneCenterOf, CFSG.Quasithin.omegaOneOf] at hmem
        exact (Subgroup.closure_le (CFSG.Quasithin.centerOf D.T)).mpr
          (fun x hx => hx.1) hmem
      exact hz1.2
    exact Subgroup.mem_centralizer_iff.mp hzC r (hR'T hr)
  have hR'CU : R' ≤ Subgroup.centralizer (U : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    refine CFSG.Quasithin.conjClosure_le ?_
    intro h hh z hz
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hconjR : h⁻¹ * r * h ∈ R' := by
      have hh1 := (Subgroup.mem_normalizer_iff.mp (hX2R' (X2.inv_mem hh)) r).1 hr
      simpa using hh1
    have hcomm := hR'Z _ hconjR z hz
    calc r * (h * z * h⁻¹) = h * ((h⁻¹ * r * h) * z) * h⁻¹ := by group
      _ = h * (z * (h⁻¹ * r * h)) * h⁻¹ := by rw [hcomm]
      _ = (h * z * h⁻¹) * r := by group
  have hTC_le_R' : D.T ⊓ Cc ≤ R' := fun _ hx => Subgroup.mem_sup_left hx
  have hsupT : (D.T ⊓ conjClosure D.M L) ⊔ R' = D.T := by
    refine le_antisymm (sup_le inf_le_left hR'T) ?_
    intro t ht
    obtain ⟨s, hs, c, hc, rfl⟩ := hTdecomp t ht
    exact ((D.T ⊓ conjClosure D.M L) ⊔ R').mul_mem
      (Subgroup.mem_sup_left hs) (Subgroup.mem_sup_right (hTC_le_R' hc))
  have hDnormR' : D.T ⊓ conjClosure D.M L ≤ Subgroup.normalizer (R' : Set G) :=
    (inf_le_left.trans le_sup_left).trans hX2R'
  have hidx1 : R'.relIndex D.T = R'.relIndex (D.T ⊓ conjClosure D.M L) := by
    have h := CFSG.Quasithin.B6.relIndex_sup_eq_of_le_normalizer (D := R')
      (T := D.T ⊓ conjClosure D.M L) hDnormR'
    rwa [hsupT] at h
  let Dm : Subgroup G := D.T ⊓ conjClosure D.M L
  have hDmstab : Dm ≤ stabTil ⊥ V := inf_le_left.trans (D.sylowM.le.trans hMstab)
  let φ : ↥Dm →* MulAut (Vtil ⊥ V hV) :=
    (actTil ⊥ V hV).comp (Subgroup.inclusion hDmstab)
  have hφrange : φ.range = barSub ⊥ V hV (D.T ⊓ conjClosure D.M L) := by
    ext y
    rw [MonoidHom.mem_range, mem_barSub]
    constructor
    · rintro ⟨d, rfl⟩
      exact ⟨⟨(d : G), hDmstab d.2⟩, d.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨(g : G), hg⟩, rfl⟩
  have hcomap : (preBarSub (conjClosure D.M L) ⊥ V hV Q).subgroupOf Dm =
      Q.comap φ := by
    ext d
    rw [Subgroup.mem_subgroupOf, mem_preBarSub, Subgroup.mem_comap]
    constructor
    · rintro ⟨-, h, hdQ⟩
      exact hdQ
    · intro hdQ
      exact ⟨d.2.2, hDmstab d.2, hdQ⟩
  have hidx3 : (preBarSub (conjClosure D.M L) ⊥ V hV Q).relIndex Dm =
      Q.relIndex (barSub ⊥ V hV D.T ⊓ barSub ⊥ V hV (conjClosure D.M L)) := by
    rw [show (preBarSub (conjClosure D.M L) ⊥ V hV Q).relIndex Dm =
      ((preBarSub (conjClosure D.M L) ⊥ V hV Q).subgroupOf Dm).index from rfl]
    rw [hcomap, ← Subgroup.relIndex_top_right (H := Q.comap φ),
      Subgroup.relIndex_comap, Subgroup.map_top, hφrange,
      EighteenElevenTransport.barSub_inf_eq hV hMstab hTsyl hXM hXn]
  have hR'idx : R'.relIndex D.T ≤ 2 ^ n := by
    rw [hidx1]
    calc R'.relIndex Dm ≤ (preBarSub (conjClosure D.M L) ⊥ V hV Q).relIndex Dm :=
          Subgroup.relIndex_le_of_le_left (L := Dm) (fun x hx => Subgroup.mem_sup_right hx)
            (Subgroup.index_ne_zero_of_finite
              (H := (preBarSub (conjClosure D.M L) ⊥ V hV Q).subgroupOf Dm))
      _ = Q.relIndex (barSub ⊥ V hV D.T ⊓ barSub ⊥ V hV (conjClosure D.M L)) := hidx3
      _ ≤ 2 ^ n := hidx
  have hTU : D.T ≤ Subgroup.normalizer (U : Set G) := le_sup_left.trans hX2U
  have hSylAut : CFSG.LargeExtraspecial.S5.IsSylowTwoIn
      (CFSG.Quasithin.autI hUel D.T) (CFSG.Quasithin.autI hUel X2) :=
    CFSG.Quasithin.B2F.isSylowTwoOf_autI hUel hX2U ⟨hS.1, hS.2.1, hS.2.2⟩
  have hTstar_le : Nat.card ↥(CFSG.Quasithin.autI hUel D.T) ≤ R'.relIndex D.T := by
    have hrel : (D.T ⊓ Subgroup.centralizer (U : Set G)).relIndex D.T *
        Nat.card ↥(D.T ⊓ Subgroup.centralizer (U : Set G)) = Nat.card ↥D.T := by
      have h := Subgroup.relIndex_mul_card (D.T ⊓ Subgroup.centralizer (U : Set G)) D.T
      rwa [inf_eq_left.mpr (inf_le_left : D.T ⊓ Subgroup.centralizer (U : Set G) ≤ D.T)] at h
    have hcard := CFSG.Quasithin.card_autI_mul_card_inf hUel hTU
    have hb : 0 < Nat.card ↥(D.T ⊓ Subgroup.centralizer (U : Set G)) := Nat.card_pos
    have heq : Nat.card ↥(CFSG.Quasithin.autI hUel D.T) =
        (D.T ⊓ Subgroup.centralizer (U : Set G)).relIndex D.T :=
      Nat.mul_right_cancel hb (hcard.trans hrel.symm)
    rw [heq]
    exact Subgroup.relIndex_le_of_le_left (L := D.T) (le_inf hR'T hR'CU)
      (Subgroup.index_ne_zero_of_finite (H := R'.subgroupOf D.T))
  have ha : CFSG.Quasithin.E3.aParam (CFSG.Quasithin.autI hUel X2) ≤ n := by
    refine CFSG.Quasithin.E3.aParam_le_of_card_le (CFSG.Quasithin.autI hUel X2)
      (n := n) fun A hAX hsq => ?_
    have hA2grp : IsPGroup 2 ↥A :=
      CFSG.Quasithin.isPGroup_two_of_forall fun a ha =>
        ⟨1, by simpa using hsq (a : MulAut (CFSG.Quasithin.IntMod U hUel)) ha⟩
    obtain ⟨S, hSylS, hAS⟩ := CFSG.LargeExtraspecial.S5.exists_isSylowTwoIn_ge hAX hA2grp
    have hcardS : Nat.card ↥S = Nat.card ↥(CFSG.Quasithin.autI hUel D.T) := by
      obtain ⟨c, -, hc⟩ := CFSG.LargeExtraspecial.S5.IsSylowTwoIn.exists_conj hSylAut hSylS
      have hmap : S.map (MulAut.conj (c⁻¹)).toMonoidHom = CFSG.Quasithin.autI hUel D.T := by
        ext y
        rw [Subgroup.mem_map]
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact (hc x).mp hx
        · intro hy
          refine ⟨c * y * c⁻¹, ?_, ?_⟩
          · rw [hc]
            show c⁻¹ * (c * y * c⁻¹) * c ∈ CFSG.Quasithin.autI hUel D.T
            simpa [mul_assoc] using hy
          · show c⁻¹ * (c * y * c⁻¹) * c = y
            group
      rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj (c⁻¹)).injective]
    calc Nat.card ↥A ≤ Nat.card ↥S := Subgroup.card_le_of_le hAS
      _ = Nat.card ↥(CFSG.Quasithin.autI hUel D.T) := hcardS
      _ ≤ R'.relIndex D.T := hTstar_le
      _ ≤ 2 ^ n := hR'idx

  have hinv : ∀ t ∈ Subgroup.normalizer
      (barSub ⊥ V hV (conjClosure D.M L) : Set (MulAut (Vtil ⊥ V hV))),
      orderOf t = 2 →
        2 * n ≤ CFSG.Quasithin.rkIdx (CFSG.Quasithin.fixV (Subgroup.zpowers t)) :=
    fun t ht ht2 => hKI (Vtil ⊥ V hV) hWsq (barSub ⊥ V hV (conjClosure D.M L)) n hodd
      hSpData t ht ht2
  have hm2n : 2 * n ≤ mBar D.M ⊥ V hV := two_mul_le_mBar_of_involution D h hSp hinv
  have hm2 : MBarGT D.M ⊥ V 2 := TwelveShort.mBarGT_mono hm3 (by norm_num)
  have hV1 : InCalV1 D.M D.T V := inCalV1_of_hyp125_bot D h.hyp125
  have hi : MBarGT D.M ⊥ V (0 + CFSG.Quasithin.E3.aParam
      (CFSG.Quasithin.autI hUel X2)) := by
    refine (h.hyp125.mBarGT_iff_lt_mBar (0 + CFSG.Quasithin.E3.aParam
      (CFSG.Quasithin.autI hUel X2))).2 ?_
    omega
  obtain ⟨-, hprod⟩ := twelve_twentyOne_one D h111 hV1 hm2 hF hS hi
  have hU0Z : U0 ≤ CFSG.Quasithin.omegaOneCenterOf D.T := by
    intro u hu
    rw [CFSG.Quasithin.omegaOneCenterOf, CFSG.Quasithin.omegaOneOf]
    exact Subgroup.subset_closure ⟨hu.2, hV.2 u hu.1⟩
  have hCZ : X2 ⊓ Subgroup.centralizer (CFSG.Quasithin.omegaOneCenterOf D.T : Set G) ≤
      D.T :=
    (inf_le_inf_left X2 (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hU0Z))).trans
      (le_of_eq hCU)
  have hTW : D.T ≤ Subgroup.normalizer (CFSG.Quasithin.E3.wClos V 0 D.T : Set G) :=
    Subgroup.le_normalizer.trans (CFSG.Quasithin.E3.normalizer_le_normalizer_wClos D.T)
  have hX2W : X2 ≤ Subgroup.normalizer (CFSG.Quasithin.E3.wClos V 0 D.T : Set G) := by
    intro x hx
    have hx' : x ∈ (X2 : Set G) := hx
    rw [hprod] at hx'
    obtain ⟨c, hc, m, hm, rfl⟩ := hx'
    exact (Subgroup.normalizer (CFSG.Quasithin.E3.wClos V 0 D.T : Set G)).mul_mem
      (hTW (hCZ hc)) hm.2
  have hW0_2 : IsPGroup 2 (CFSG.Quasithin.E3.wClos V 0 D.T) :=
    D.sylowM.isPGroup.to_le (CFSG.Quasithin.E3.wClos_le 0 D.T)
  have hVrk : 0 < CFSG.Quasithin.rk ↥V := by
    have hV2 : IsPGroup 2 V := CFSG.Open.IsElemAbelian.isPGroup hV
    have hcard : Nat.card V = 2 ^ CFSG.Quasithin.rk ↥V :=
      CFSG.Quasithin.card_eq_two_pow_of_isPGroup hV2
    have h1 : 1 < Nat.card V := by
      rw [Finite.one_lt_card_iff_nontrivial]
      exact (Subgroup.nontrivial_iff_ne_bot V).mpr hVne
    by_contra h0
    rw [Nat.not_lt] at h0
    have hz : CFSG.Quasithin.rk ↥V = 0 := by omega
    rw [hcard, hz, pow_zero] at h1
    omega
  have hW0ne : CFSG.Quasithin.E3.wClos V 0 D.T ≠ ⊥ :=
    CFSG.Quasithin.E3.wClos_ne_bot hV hVT hVrk
  have hH : CFSG.Open.IsTwoLocal
      (Subgroup.normalizer (CFSG.Quasithin.E3.wClos V 0 D.T : Set G)) :=
    ⟨_, hW0ne, hW0_2, rfl⟩
  obtain ⟨b, hbord, c, hbact⟩ :=
    exists_lift_prime_order h.hyp125 hXstab hXsub hsimple hX1 hr hr2 (hPH hb₂P) hord₂
  have hord₂' : orderOf (b₂ ^ 2 ^ c) = r := by
    rw [orderOf_pow, hord₂,
      Nat.Coprime.gcd_eq_one
        (Nat.Coprime.pow_right c (Nat.coprime_two_right.mpr (hr.odd_of_ne_two hr2))),
      Nat.div_one]
  have hconj₂' : x₂ * (b₂ ^ 2 ^ c) * x₂⁻¹ = (b₂ ^ 2 ^ c)⁻¹ := by
    rw [← conj_pow, hconj₂, inv_pow]
  have hY₂' : Y₂ ≤ barSub ⊥ V hV (conjClosure D.M L) ⊓
      Subgroup.centralizer ({b₂ ^ 2 ^ c} : Set (MulAut (Vtil ⊥ V hV))) := by
    refine hY₂.trans (le_inf inf_le_left ?_)
    intro y hy
    have hy' : Commute y b₂ := Subgroup.mem_centralizer_singleton_iff.mp hy.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hy'.pow_right _
  have hbN : actTil ⊥ V hV ⟨(b : G), hXstab b.2⟩ ∈
      Subgroup.normalizer
        (barSub ⊥ V hV (D.T ⊓ conjClosure D.M L) : Set (MulAut (Vtil ⊥ V hV))) := by
    rw [hbact]
    have hS : b₂ ∈ Subgroup.normalizer
        (barSub ⊥ V hV (D.T ⊓ conjClosure D.M L) : Set (MulAut (Vtil ⊥ V hV))) := by
      rw [← EighteenElevenTransport.barSub_inf_eq hV hMstab hTsyl hXM hXn]
      exact hb₂S
    exact (Subgroup.normalizer _).pow_mem hS _
  have hbcard : Nat.card ↥(Subgroup.zpowers (b : G)) = r := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe]
    exact hbord
  have hpow := (hpow_and_inner_of_isSp4 D hXc hTL hns hodd hSpBar2 hZ).2
  have hBT : Subgroup.zpowers (b : G) ≤ Subgroup.normalizer (D.T : Set G) :=
    S17.le_normalizer_of_le_borel hTL D.sylowM.isPGroup hpow hodd hr hrdvd
      (Subgroup.zpowers_le.mpr ⟨b.2, normalizer_inf_of_actTil_mem_normalizer D h
        hsimple hX1 b.2 (hXstab b.2) hbN⟩) hbcard
  have hbP2 : (b : G) ∈ P2 := by
    refine (mem_preBarSub (conjClosure D.M L) ⊥ V hV P).2
      ⟨b.2, hXstab b.2, ?_⟩
    rw [hbact]
    exact P.pow_mem hb₂P _
  have hconjbar : x₂ * actTil ⊥ V hV ⟨(b : G), hXstab b.2⟩ * x₂⁻¹ =
      (actTil ⊥ V hV ⟨(b : G), hXstab b.2⟩) ^ (-1 : ℤ) := by
    rw [zpow_neg_one, hbact]
    exact hconj₂'
  obtain ⟨x, hxact, hxconj⟩ :=
    exists_lift_conj_pow (m := -1) h.hyp125 hXstab hXsub hsimple hX1 hbord hr hr2
      (hPH hx₂P) hconjbar
  have hxP2 : (x : G) ∈ P2 := by
    refine (mem_preBarSub (conjClosure D.M L) ⊥ V hV P).2
      ⟨x.2, hXstab x.2, ?_⟩
    rw [hxact]
    exact hx₂P
  have hY₂'' : Y₂ ≤ barSub ⊥ V hV (conjClosure D.M L) ⊓
      Subgroup.centralizer ({actTil ⊥ V hV ⟨(b : G), hXstab b.2⟩} :
        Set (MulAut (Vtil ⊥ V hV))) := by
    rw [hbact]
    exact hY₂'
  obtain ⟨Yt, hYtX, N₀, hN₀, hL2Yt⟩ :=
    exists_L2_section_of_lift h.hyp125 hXstab hXsub hsimple hX1 hbord hr hr2 hY₂'' hL2Y₂
  have hp' : p.Prime := (D.sig_prime p h.hp).1
  have hp2 : p ≠ 2 := (D.sig_prime p h.hp).2
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M :=
    UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hXc) h.hp
  have h3 : 3 ≤ CFSG.Open.pRank p D.M := hSg.three_le p h.hp
  have hOp : UC22.F10.OpRes p D.M = D.M := h638 p hp' hp2 (Or.inl h.hp)
  obtain ⟨hCB, hBU⟩ :=
    S17.centralizer_le_and_mem_uniqueSet_of_rootLine h72 hK35 h.hp hsp h3 hOp hn3 hpn hZ hOut
      hr hr2 hXr hpX hN₀ hL2Yt (Subgroup.zpowers_le.mpr b.2) hbcard hYtX hrankE
  have hxconjG : (x : G) * (b : G) * (x : G)⁻¹ = (b : G)⁻¹ := by
    have h := congrArg Subtype.val hxconj
    simpa [zpow_neg_one] using h
  have hK2P2 : Subgroup.zpowers (b : G) ⊔ Subgroup.zpowers (x : G) ≤ P2 :=
    sup_le (Subgroup.zpowers_le.mpr hbP2) (Subgroup.zpowers_le.mpr hxP2)
  have hKH : (Subgroup.zpowers (b : G) ⊔ Subgroup.zpowers (x : G)) ⊔ D.T ≤
      Subgroup.normalizer (CFSG.Quasithin.E3.wClos V 0 D.T : Set G) :=
    sup_le (hK2P2.trans (hP2X2.trans hX2W)) hTW
  exact le_M_of_twoLocal_of_inverted D h109 hodd hr hrdvd
    (le_inf (Subgroup.zpowers_le.mpr (hXM b.2)) hBT) hbcard hBU le_sup_left
    (hK2P2.trans hP2M) (invertedIn_sup_zpowers hxconjG) hH hKH


end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
