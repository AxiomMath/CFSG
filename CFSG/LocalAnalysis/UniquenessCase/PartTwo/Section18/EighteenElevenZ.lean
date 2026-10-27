module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenElevenSp4Setup
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenElevenLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TwoNatHolds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin (IsSylowIn)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

section Certified


theorem gap_18_11_Z_of (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (h1742 : S17.R17_42At D V₀ V)
    (h6b : R18_6bAt D V₀ V p L h) (h7b : R18_7bAt D V₀ V p L h)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3)
    (h8 : R18_8At D V₀ V p L h) (h9 : R18_9At D V₀ V p L h)
    (h10 : R18_10At D V₀ V p L h)
    (hKns : K_Sp4TwoNat_noSwap) (hSg : UC6S846.SigmaStd D) (h638 : UC6.R6_38 D)
    (h72 : F07.R72 D) (hK35 : UCK.K35w) (h109 : UC2_10_9 D) :
    Gap_18_11_Z D V₀ V p L h := by
  rintro ⟨n, hSp⟩ hV0
  subst hV0
  classical
  have hV : IsElemAbelian 2 V := h.hyp125.isElemAbelian
  have hMnorm : D.M ≤ Subgroup.normalizer (V : Set G) := h.hyp125.pairFacts.le_normalizer
  have hMnorm₀ : D.M ≤ Subgroup.normalizer (⊥ : Subgroup G) := by
    simpa using h.hyp125.pairFacts.le_normalizer₀
  have hMstab : D.M ≤ stabTil (⊥ : Subgroup G) V := le_stabTil hMnorm hMnorm₀
  have hXM : conjClosure D.M L ≤ D.M := TwelveTwentyThree.conjClosure_le h.hL.1.1.le
  have hXn : ((conjClosure D.M L).subgroupOf D.M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXM).mpr
      (TwelveTwentyThree.le_normalizer_conjClosure D.M L)
  have hTm : IsSylowIn 2 D.T D.M := CFSG.ABGLocalTools.isSylowOf_iff.mp D.sylowM
  have hT2 : IsPGroup 2 D.T := D.sylowM.isPGroup
  have hXstab : conjClosure D.M L ≤ stabTil (⊥ : Subgroup G) V := hXM.trans hMstab
  have hXsub : CFSG.Open.IsSubnormal (conjClosure D.M L) D.M :=
    CFSG.Quasithin.A3.subnormal_of_normal hXM hXn
  have hTL : D.T ≤ Subgroup.normalizer (conjClosure D.M L : Set G) :=
    D.sylowM.le.trans (TwelveTwentyThree.le_normalizer_conjClosure D.M L)
  have hSpBar2 : IsSp4 (Bar2 (conjClosure D.M L)) n := isSp4_bar2_of_isSp4_barSub h hSp
  have hsBar2 : IsSimpleGroup (Bar2 (conjClosure D.M L)) :=
    LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hSpBar2
  have hXL : conjClosure D.M L = L := conjClosure_eq_self_of_isSimpleGroup_bar2 h.hL.1 hsBar2
  have hXc : conjClosure D.M L ∈ calC D.M := by
    rw [hXL]; exact h.hL.1
  let Xbar : Subgroup (MulAut (Vtil (⊥ : Subgroup G) V hV)) :=
    barSub (⊥ : Subgroup G) V hV (conjClosure D.M L)
  have hsXbar : IsSimpleGroup Xbar :=
    LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hSp
  have hX1 : Xbar ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot Xbar).mp hsXbar.toNontrivial
  obtain ⟨⟨r, hr, hr7, hrdvd, hXopp, hrankE⟩, hpX, hn3, -, hpn, hZ, hOut⟩ :=
    sp4_rootLine_setup D h h1742 hSp
  have hr2 : r ≠ 2 := by omega
  have hodd : Odd n := by
    obtain ⟨-, -, -, hodd, -, -, -⟩ :=
      isSp4_or_isG2_bar2_cong_more h h1742 (Or.inl hSpBar2)
    exact hodd
  have hm3 : MBarGT D.M (⊥ : Subgroup G) V 3 := h1669 (by simp)
  have hns := not_swapsParabolics_of_isSp4_df D h hm3 h6b h7b h8 h9 h10 hSp hKns
  have hpow := (hpow_and_inner_of_isSp4 D hXc hTL hns hodd hSpBar2 hZ).2
  have hSpData : Sp4TwoNatData Xbar n := by
    obtain ⟨-, hdata⟩ := sp4Data_of_df D h hm3 h6b h7b h8 h9 h10 hSp
    exact ⟨hSp, hdata⟩
  have hSsyl0 : IsSylowIn 2 (barSub (⊥ : Subgroup G) V hV D.T ⊓ Xbar) Xbar :=
    EighteenElevenTransport.barSub_inf_isSylow hV hMstab hTm hXM hXn
  have hbarEq : barSub (⊥ : Subgroup G) V hV D.T ⊓ Xbar =
      barSub (⊥ : Subgroup G) V hV (D.T ⊓ conjClosure D.M L) :=
    EighteenElevenTransport.barSub_inf_eq hV hMstab hTm hXM hXn
  have hSsyl : IsSylowIn 2
      (barSub (⊥ : Subgroup G) V hV (D.T ⊓ conjClosure D.M L)) Xbar := by
    rw [← hbarEq]; exact hSsyl0
  obtain ⟨b, hbH, x, hxH, Y, hbN, hborder, hbfix, hxfix, hbinv, hY, hYL2⟩ :=
    k_Sp4TwoNat_pointTorus_holds (Vtil (⊥ : Subgroup G) V hV)
      (s15_Infra_vtil_sq_eq_one (⊥ : Subgroup G) V hV)
      Xbar (barSub (⊥ : Subgroup G) V hV (D.T ⊓ conjClosure D.M L)) n r
      hSpData hSsyl hr hrdvd
  obtain ⟨bG, hbGord, c, hbGact⟩ :=
    exists_lift_prime_order h.hyp125 hXstab hXsub hsBar2 hX1 hr hr2 hbH hborder
  have h2r : Nat.Coprime r 2 :=
    (Nat.Prime.coprime_iff_not_dvd hr).mpr (fun h2dvd =>
      hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h2dvd))
  have hcop : Nat.Coprime r (2 ^ c) := Nat.Coprime.pow_right c h2r
  have hborder' : orderOf (b ^ 2 ^ c) = r := by
    rw [Nat.Coprime.orderOf_pow (y := b) (m := 2 ^ c)]
    · exact hborder
    · rwa [hborder]
  have hbfix' : ∀ w ∈ CFSG.Quasithin.fixV
      (barSub (⊥ : Subgroup G) V hV (D.T ⊓ conjClosure D.M L)), (b ^ 2 ^ c) w = w := by
    intro w hw
    have hpowfix : ∀ k : ℕ, (b ^ k) w = w := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => rw [pow_succ, MulAut.mul_apply, hbfix w hw, ih]
    exact hpowfix (2 ^ c)
  have hY' : Y ≤ Xbar ⊓ Subgroup.centralizer
      ({b ^ 2 ^ c} : Set (MulAut (Vtil (⊥ : Subgroup G) V hV))) := by
    refine le_inf (hY.trans inf_le_left) ?_
    intro y hy
    have hyC := (hY hy).2
    have hyC' : y ∈ Subgroup.centralizer
        ({b} : Set (MulAut (Vtil (⊥ : Subgroup G) V hV))) := hyC
    rw [Subgroup.mem_centralizer_iff] at hyC'
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    have hcomm : Commute y b := (hyC' b (Set.mem_singleton b)).symm
    exact (hcomm.pow_right (2 ^ c)).eq.symm
  have hYlift : Y ≤ Xbar ⊓ Subgroup.centralizer
      ({actTil (⊥ : Subgroup G) V hV ⟨(bG : G), hXstab bG.2⟩} :
        Set (MulAut (Vtil (⊥ : Subgroup G) V hV))) := by
    rw [hbGact]
    exact hY'
  have hbinv' : x * (b ^ 2 ^ c) * x⁻¹ = (b ^ 2 ^ c)⁻¹ := by
    calc x * (b ^ 2 ^ c) * x⁻¹ = (MulAut.conj x) (b ^ 2 ^ c) :=
          (MulAut.conj_apply x (b ^ 2 ^ c)).symm
      _ = ((MulAut.conj x) b) ^ (2 ^ c) := map_pow (MulAut.conj x) b (2 ^ c)
      _ = (b⁻¹) ^ (2 ^ c) := by rw [MulAut.conj_apply, hbinv]
      _ = (b ^ 2 ^ c)⁻¹ := inv_pow b (2 ^ c)
  have hconj : x * actTil (⊥ : Subgroup G) V hV ⟨(bG : G), hXstab bG.2⟩ * x⁻¹ =
      (actTil (⊥ : Subgroup G) V hV ⟨(bG : G), hXstab bG.2⟩) ^ (-1 : ℤ) := by
    rw [hbGact, zpow_neg_one]
    exact hbinv'
  obtain ⟨xG, hxGact, hxGinv⟩ :=
    exists_lift_conj_pow h.hyp125 hXstab hXsub hsBar2 hX1 hbGord hr hr2 hxH
      (m := (-1 : ℤ)) hconj
  have hxGinv' : xG * bG * xG⁻¹ = bG⁻¹ := by
    rw [zpow_neg_one] at hxGinv
    exact hxGinv
  have hxGinvG : (xG : G) * (bG : G) * (xG : G)⁻¹ = (bG : G)⁻¹ := by
    have h := congrArg (fun y : ↥(conjClosure D.M L) => (y : G)) hxGinv'
    simpa using h
  obtain ⟨Yt, hYt, N₀, hN₀, hL2sec⟩ :=
    exists_L2_section_of_lift h.hyp125 hXstab hXsub hsBar2 hX1 hbGord hr hr2 hYlift hYL2
  have hbn : actTil (⊥ : Subgroup G) V hV ⟨(bG : G), hXstab bG.2⟩ ∈
      Subgroup.normalizer
        (barSub (⊥ : Subgroup G) V hV (D.T ⊓ conjClosure D.M L) :
          Set (MulAut (Vtil (⊥ : Subgroup G) V hV))) := by
    rw [hbGact]
    exact Subgroup.pow_mem _ hbN (2 ^ c)
  have hB1 : (bG : G) ∈ Subgroup.normalizer
      ((D.T ⊓ conjClosure D.M L : Subgroup G) : Set G) :=
    normalizer_inf_of_actTil_mem_normalizer D h hsBar2 hX1 bG.2 (hXstab bG.2) hbn
  let B : Subgroup G := Subgroup.zpowers (bG : G)
  let K : Subgroup G := B ⊔ Subgroup.zpowers (xG : G)
  have hBcard : Nat.card B = r := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hbGord]
  have hBorel : B ≤ conjClosure D.M L ⊓
      Subgroup.normalizer ((D.T ⊓ conjClosure D.M L : Subgroup G) : Set G) := by
    refine le_inf (Subgroup.zpowers_le.mpr bG.2) (Subgroup.zpowers_le.mpr hB1)
  have hBT : B ≤ Subgroup.normalizer (D.T : Set G) :=
    S17.le_normalizer_of_le_borel hTL hT2 hpow hodd hr hrdvd hBorel hBcard
  have hKM : K ≤ D.M := by
    refine sup_le ((Subgroup.zpowers_le.mpr bG.2).trans hXM)
      ((Subgroup.zpowers_le.mpr xG.2).trans hXM)
  have hBM : B ≤ D.M := (Subgroup.zpowers_le.mpr bG.2).trans hXM
  have hB : B ≤ D.M ⊓ Subgroup.normalizer (D.T : Set G) := le_inf hBM hBT
  have hp' : p.Prime := (D.sig_prime p h.hp).1
  have hp2 : p ≠ 2 := (D.sig_prime p h.hp).2
  have hsp : IsStronglyPEmbedded p D.M :=
    UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC h.hL.1) h.hp
  have h3 : 3 ≤ CFSG.Open.pRank p D.M := hSg.three_le p h.hp
  have hOp : UC22.F10.OpRes p D.M = D.M := h638 p hp' hp2 (Or.inl h.hp)
  have hroot := S17.centralizer_le_and_mem_uniqueSet_of_rootLine h72 hK35 h.hp hsp h3 hOp
    hn3 hpn hZ hOut hr hr2 hXopp hpX hN₀ hL2sec (Subgroup.zpowers_le.mpr bG.2) hBcard hYt
    hrankE
  obtain ⟨-, hBU⟩ := hroot
  let U₀ : Subgroup G := V ⊓ CFSG.Quasithin.centerOf D.T
  have hU0mem : ∀ u : G, u ∈ U₀ ↔
      u ∈ V ∧ u ∈ D.T ∧ u ∈ Subgroup.centralizer (D.T : Set G) := by
    intro u
    change u ∈ V ⊓ CFSG.Quasithin.centerOf D.T ↔ _
    simp only [Subgroup.mem_inf, CFSG.Quasithin.centerOf]
  have hVT : V ≤ D.T := uc22p22p_le_T_of_inCalV D h.hyp125.inCalV
  have hTV : D.T ≤ Subgroup.normalizer (V : Set G) := D.sylowM.le.trans hMnorm
  have hU0ne : U₀ ≠ ⊥ := by
    have h := uc22p22na_inf_center_ne_bot (T := D.T) (V := V) hT2 hVT hTV
      h.hyp125.pairFacts.ne_bot
    have hEq : U₀ = V ⊓ (D.T ⊓ Subgroup.centralizer (D.T : Set G)) := by
      change V ⊓ CFSG.Quasithin.centerOf D.T = _
      rw [CFSG.Quasithin.centerOf]
    rwa [hEq]
  have hU0P : IsPGroup 2 U₀ :=
    hT2.to_le (fun u hu => ((hU0mem u).mp hu).2.1)
  have hU0Z : U₀ ≤ F11.Omega1p 2 (CFSG.Quasithin.centerOf D.T) := by
    intro u hu
    obtain ⟨huV, huT, huC⟩ := (hU0mem u).mp hu
    rw [F11.Omega1p]
    exact Subgroup.subset_closure
      ⟨Subgroup.mem_inf.mpr ⟨huT, huC⟩, hV.2 u huV⟩
  have hfixb : ∀ w ∈ CFSG.Quasithin.fixV
      (barSub (⊥ : Subgroup G) V hV (D.T ⊓ conjClosure D.M L)),
      actTil (⊥ : Subgroup G) V hV ⟨(bG : G), hXstab bG.2⟩ w = w := by
    intro w hw
    rw [hbGact]
    exact hbfix' w hw
  have hfixx : ∀ w ∈ CFSG.Quasithin.fixV
      (barSub (⊥ : Subgroup G) V hV (D.T ⊓ conjClosure D.M L)),
      actTil (⊥ : Subgroup G) V hV ⟨(xG : G), hXstab xG.2⟩ w = w := by
    intro w hw
    rw [hxGact]
    exact hxfix w hw
  have hbcent := centralizes_omegaCenter_of_actTil_fixV D h (hXstab bG.2) hfixb
  have hxcent := centralizes_omegaCenter_of_actTil_fixV D h (hXstab xG.2) hfixx
  have hbU : (bG : G) ∈ Subgroup.centralizer (U₀ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have h1 : (bG : G) * u = u * (bG : G) := by
      calc (bG : G) * u = ((bG : G) * u * (bG : G)⁻¹) * (bG : G) := by group
        _ = u * (bG : G) := by rw [hbcent u hu]
    exact h1.symm
  have hxU : (xG : G) ∈ Subgroup.centralizer (U₀ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have h1 : (xG : G) * u = u * (xG : G) := by
      calc (xG : G) * u = ((xG : G) * u * (xG : G)⁻¹) * (xG : G) := by group
        _ = u * (xG : G) := by rw [hxcent u hu]
    exact h1.symm
  have hKcent : K ≤ Subgroup.centralizer (U₀ : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr hbU) (Subgroup.zpowers_le.mpr hxU)
  have hKN : K ≤ Subgroup.normalizer (U₀ : Set G) :=
    hKcent.trans (Subgroup.centralizer_le_normalizer (U₀ : Set G))
  have hTfix : ∀ t ∈ D.T, ∀ u ∈ U₀, t * u * t⁻¹ = u := by
    intro t ht u hu
    obtain ⟨-, -, huC⟩ := (hU0mem u).mp hu
    have hut : t * u = u * t := Subgroup.mem_centralizer_iff.mp huC t ht
    calc t * u * t⁻¹ = (u * t) * t⁻¹ := by rw [hut]
      _ = u := by group
  have hTN : D.T ≤ Subgroup.normalizer (U₀ : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · intro hu
      rw [hTfix t ht u hu]
      exact hu
    · intro hu
      have h1 : u = t⁻¹ * (t * u * t⁻¹) * t := by group
      have h2 : t⁻¹ * (t * u * t⁻¹) * t = t * u * t⁻¹ := by
        simpa using hTfix t⁻¹ (D.T.inv_mem ht) (t * u * t⁻¹) hu
      rw [h1, h2]
      exact hu
  have hKH : K ⊔ D.T ≤ Subgroup.normalizer (U₀ : Set G) := sup_le hKN hTN
  have hH : CFSG.Open.IsTwoLocal (Subgroup.normalizer (U₀ : Set G)) :=
    ⟨U₀, hU0ne, hU0P, rfl⟩
  have hinv : UC22.F05.InvertedIn K B :=
    show UC22.F05.InvertedIn (Subgroup.zpowers (bG : G) ⊔ Subgroup.zpowers (xG : G))
      (Subgroup.zpowers (bG : G)) from invertedIn_sup_zpowers hxGinvG
  have hNM : Subgroup.normalizer (U₀ : Set G) ≤ D.M :=
    le_M_of_twoLocal_of_inverted D h109 (s := n) (p := r) (B := B) (K := K)
      hodd hr hrdvd hB hBcard hBU le_sup_left hKM hinv hH hKH
  intro g hg
  exact hNM ((Subgroup.centralizer_le (fun u hu => hU0Z hu)).trans
    (Subgroup.centralizer_le_normalizer (U₀ : Set G)) hg)

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
