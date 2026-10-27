module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTwoD
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenFiveTen
public import CFSG.Quasithin.Background.Asc81cTenFourA
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplitRank
public import CFSG.Adapters.LieModelSimple
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.ClassicalInvolution.QuaternionStructure
public import CFSG.GF2Type.Aschbacher1976Full.HSGL3
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.IVK.L2.SLAut
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Closed
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Statements
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Defs
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Ext
public import CFSG.GH74.GLS.Stage2.Final.LayerFDerive
public import CFSG.GH74.Orders.Sporadic
public import CFSG.LargeExtraspecial.S8CBFSect
public import CFSG.LargeExtraspecial.S8CBFSmall
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenE6
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddE6
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModelCases
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Five
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.D8
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatEvenOuterPSL
public import CFSG.LocalAnalysis.WeakClosure81.EightEight
public import CFSG.LocalAnalysis.WeakClosure81.EightEighteen
public import CFSG.LocalAnalysis.WeakClosure81.EightEleven
public import CFSG.LocalAnalysis.WeakClosure81.EightNVBasic
public import CFSG.LocalAnalysis.WeakClosure81.EightNVOmega
public import CFSG.LocalAnalysis.WeakClosure81.EightSeventeen
public import CFSG.LocalAnalysis.WeakClosure81.EightTen
public import CFSG.LocalAnalysis.WeakClosure81.EightTenAux
public import CFSG.LocalAnalysis.WeakClosure81.EightTenPrime
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenAMain
public import CFSG.LocalAnalysis.WeakClosure81.EightTwelve
public import CFSG.LocalAnalysis.WeakClosure81.EightTwelveBridge
public import CFSG.LocalAnalysis.WeakClosure81.SevenNineDefs
public import CFSG.LocalAnalysis.WeakClosure81.TwelveMinimal
public import CFSG.LocalAnalysis.WeakClosure81.TwelveTwoBridge
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.C1GNSolvConnect
public import CFSG.Quasithin.Background.C2A3Orbits
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.EmptyFaithful.S14117
public import CFSG.Quasithin.EmptyFaithful.S14117Coprime
public import CFSG.Quasithin.EmptyFaithful.S14117Rank
public import CFSG.Quasithin.EmptyFaithful.S1417Glue
public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.Quasithin.EmptyFaithful.S151cA2
public import CFSG.Quasithin.EmptyFaithful.S151cCases
public import CFSG.Quasithin.EmptyFaithful.S152UGen
public import CFSG.Quasithin.EmptyFaithful.T1515Top9
public import CFSG.Quasithin.EmptyFaithful.T1515cE
public import CFSG.Quasithin.EmptyFaithful.T1515dA
public import CFSG.Quasithin.EmptyFaithful.T1515dE
public import CFSG.Quasithin.H13.J4Core
public import CFSG.Quasithin.H13.L1332Inputs
public import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ConjugatedInvertedSubgroup
public import CFSG.Timmesfeld.Bridge.RootSetsSolv
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def K_QuasisimpleFixHalf : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ L : Subgroup (MulAut W), CFSG.Open.IsKGroup ↥L → CFSG.Open.IsQuasisimple ↥L →
      ∀ U : Subgroup W, StableUnder L U → CFSG.Quasithin.commSub U L = U →
        3 * CFSG.Quasithin.rk ↥(U ⊓ CFSG.Quasithin.fixV L) ≤ CFSG.Quasithin.rk ↥U

theorem three_le_gamma15_of_not_solvable (D : Data G) (h1217 : R1217 D)
    {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hsolv : ¬ Group.IsSolvable ↥(barSub V₀ V h.isElemAbelian L)) :
    3 ≤ gamma15 D.M V₀ V h.isElemAbelian L := by
  have hL : barSub V₀ V h.isElemAbelian L ≠ ⊥ := by
    intro hbot
    apply hsolv
    haveI : Subsingleton ↥(barSub V₀ V h.isElemAbelian L) := by
      rw [hbot]
      infer_instance
    exact Group.isSolvable_of_comm fun a b => Subsingleton.elim (a * b) (b * a)
  have h2 := two_le_gamma15 D h h.isElemAbelian hL
  by_contra h3
  have hγ : gamma15 D.M V₀ V h.isElemAbelian L = 2 := by omega
  have hcard : Nat.card ↥(barSub V₀ V h.isElemAbelian L) = 3 :=
    s15_TwoD_card_eq_three D h1217 h h.isElemAbelian hL hγ
  apply hsolv
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsCyclic ↥(barSub V₀ V h.isElemAbelian L) :=
    isCyclic_of_prime_card hcard
  exact Group.isSolvable_of_comm fun a b =>
    (isCyclic_of_prime_card hcard).isMulCommutative.is_comm.comm a b

theorem mQuot_eq_rk_sub {V U : Subgroup G} (hUV : U ≤ V) :
    E3.mQuot V U = rk ↥V - rk ↥U := by
  have h1 := rk_add_rkIdx (U.subgroupOf V)
  have h2 : rk ↥(U.subgroupOf V) = rk ↥U := CFSG.LocalAnalysis.WeakClosure81.rk_subgroupOf_eq hUV
  have h3 : rkIdx (U.subgroupOf V) = E3.mQuot V U := (E3.mQuot_eq_rkIdx V U).symm
  rw [h2, h3] at h1
  omega

theorem mQuot_inf_eq_rk_sub' {Y C : Subgroup G} :
    E3.mQuot Y (Y ⊓ C) = rk ↥Y - rk ↥(Y ⊓ C) :=
  mQuot_eq_rk_sub inf_le_left

theorem mBar_le_gamma15 (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hδ : delta15 D.M V₀ V h.isElemAbelian L ≤ 1)
    (hact : ∃ t ∈ barSub V₀ V h.isElemAbelian L, orderOf t = 2 ∧
      ¬ wTil V₀ V h.isElemAbelian L ≤ fixV (Subgroup.zpowers t)) :
    mBar D.M V₀ V h.isElemAbelian ≤ gamma15 D.M V₀ V h.isElemAbelian L := by
  obtain ⟨t, htL, hto, htfix⟩ := hact
  have hV := h.isElemAbelian
  have ht2 : t ^ 2 = 1 := by
    have := pow_orderOf_eq_one t
    rwa [hto] at this
  have hzp : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hto]; norm_num)
  have hzple : Subgroup.zpowers t ≤ Mbar D.M V₀ V hV :=
    (Subgroup.zpowers_le.mpr htL).trans (barSub_mono V₀ V hV h.le)
  have hzpne : Subgroup.zpowers t ≠ ⊥ := by
    intro hbot
    have ht1 : t = 1 := by
      have : t ∈ Subgroup.zpowers t := Subgroup.mem_zpowers t
      rw [hbot] at this
      exact Subgroup.mem_bot.1 this
    rw [ht1] at hto
    simp at hto
  have hmbar := E3.mParam_le_rkIdx_fixV hzple hzp hzpne
  rw [CFSG.Quasithin.rkIdx_fixV_zpowers, CFSG.Quasithin.commV_eq_commSub] at hmbar
  set B : Subgroup (Vtil V₀ V hV) := CFSG.Quasithin.commSub ⊤ (Subgroup.zpowers t) with hB
  set Wt : Subgroup (Vtil V₀ V hV) := wTil V₀ V hV L with hWt
  set U : Subgroup (Vtil V₀ V hV) :=
    imgTil V₀ V hV (v1Sub D.M V₀ V hV L ⊓ wSub V₀ V hV L) with hU
  have hBW : B ≤ Wt := by
    rw [hB, hWt]
    exact CFSG.Quasithin.commSub_mono le_rfl (Subgroup.zpowers_le.mpr htL)
  have hUW : U ≤ Wt := by
    have h := Subgroup.map_mono (f := (mkTil V₀ V hV))
      (Subgroup.subgroupOf_mono V
        (inf_le_right : v1Sub D.M V₀ V hV L ⊓ wSub V₀ V hV L ≤ wSub V₀ V hV L))
    change imgTil V₀ V hV (v1Sub D.M V₀ V hV L ⊓ wSub V₀ V hV L) ≤
      imgTil V₀ V hV (wSub V₀ V hV L) at h
    rw [wSub, imgTil_preTil] at h
    rwa [hWt]
  have hfixU : U ≤ fixV (Subgroup.zpowers t) := by
    have h1 : imgTil V₀ V hV (v1Sub D.M V₀ V hV L) ≤
        fixV (barSub V₀ V hV L) := by
      simpa only [conjSubgroup_one] using
        s15_Core_imgTil_v1Sub_le_fixV h (m := (1 : G)) D.M.one_mem
    have h0 := Subgroup.map_mono (f := (mkTil V₀ V hV))
      (Subgroup.subgroupOf_mono V
        (inf_le_left : v1Sub D.M V₀ V hV L ⊓ wSub V₀ V hV L ≤ v1Sub D.M V₀ V hV L))
    change imgTil V₀ V hV (v1Sub D.M V₀ V hV L ⊓ wSub V₀ V hV L) ≤
      imgTil V₀ V hV (v1Sub D.M V₀ V hV L) at h0
    exact (h0.trans h1).trans (CFSG.Quasithin.fixV_anti (Subgroup.zpowers_le.mpr htL))
  have hfixB : B ≤ fixV (Subgroup.zpowers t) := by
    have hsq := s15_Infra_vtil_sq_eq_one V₀ V hV
    exact (CFSG.Quasithin.commSub_zpowers_le_inf_fixV hsq ht2
      (W := (⊤ : Subgroup (Vtil V₀ V hV))) (fun _ _ _ _ => Subgroup.mem_top _)).trans inf_le_right
  have hne : B ⊔ U ≠ Wt := by
    intro hsup
    exact htfix (hsup ▸ sup_le hfixB hfixU)
  have hWt2 : IsPGroup 2 Wt :=
    CFSG.Quasithin.isPGroup_two_of_sq_eq_one
      (fun w : Wt => Subtype.ext (by
        simpa using s15_Infra_vtil_sq_eq_one V₀ V hV (w : Vtil V₀ V hV)))
  have hpos : 0 < E3.mQuot Wt (B ⊔ U) := by
    rcases Nat.eq_zero_or_pos (E3.mQuot Wt (B ⊔ U)) with h0 | h0
    · exact absurd ((E3.mQuot_eq_zero_iff hWt2 (sup_le hBW hUW)).1 h0) hne
    · exact h0
  have hadd := E3.mQuot_add (V := Wt) (U := U) (U' := B ⊔ U) le_sup_right
    (sup_le hBW hUW)
  have hsplit : E3.mQuot (B ⊔ U) U = E3.mQuot B (B ⊓ U) := by
    unfold E3.mQuot
    have h1 : U.relIndex (U ⊔ B) = U.relIndex B := by
      rw [sup_comm U B]
      exact Subgroup.relIndex_sup_right B U
    have h2 : U.relIndex B = (B ⊓ U).relIndex B := by
      rw [← Subgroup.inf_relIndex_right (H := U) (K := B), inf_comm U B]
    rw [sup_comm B U, h1, h2]
  have hBrank : rk ↥B = E3.mQuot B (B ⊓ U) + rk ↥(B ⊓ U) := by
    have hsub := mQuot_inf_eq_rk_sub' (Y := B) (C := U)
    have hle : rk ↥(B ⊓ U) ≤ rk ↥B := rk_mono inf_le_left
    omega
  have hUle : rk ↥U ≤ delta15 D.M V₀ V hV L := by
    have h1 := s15_Infra_mSub_eq_rk_imgTil_add V₀ V
      (v1Sub D.M V₀ V hV L ⊓ wSub V₀ V hV L) hV
      (inf_le_right.trans (preTil_le V₀ V hV _))
    have hW0 : V₀ ≤ wSub V₀ V hV L := by
      intro v hv0
      rw [wSub, mem_preTil_iff_of_mem V₀ V hV _ (h.hyp125.pairFacts.le hv0)]
      have hvmod : IntMod.mk hV ⟨v, h.hyp125.pairFacts.le hv0⟩ ∈ modNull V₀ V hV := by
        rw [mem_modNull]
        exact hv0
      rw [show mkTil V₀ V hV (IntMod.mk hV ⟨v, h.hyp125.pairFacts.le hv0⟩) = 1 from
        (QuotientGroup.eq_one_iff (N := modNull V₀ V hV) _).2 hvmod]
      exact (wTil V₀ V hV L).one_mem
    have h2 : (v1Sub D.M V₀ V hV L ⊓ wSub V₀ V hV L) ⊓ V₀ = V₀ := by
      rw [inf_assoc, inf_eq_right.mpr hW0]
      exact inf_eq_right.mpr (s15_Infra_le_v1Sub D.M V₀ V hV L)
    change mSub (v1Sub D.M V₀ V hV L ⊓ wSub V₀ V hV L) =
      rk ↥U + mSub ((v1Sub D.M V₀ V hV L ⊓ wSub V₀ V hV L) ⊓ V₀) at h1
    rw [h2] at h1
    rw [delta15]
    omega
  have hWtU : E3.mQuot Wt U = gamma15 D.M V₀ V hV L := by
    have hW0 : V₀ ≤ wSub V₀ V hV L := by
      intro v hv0
      rw [wSub, mem_preTil_iff_of_mem V₀ V hV _ (h.hyp125.pairFacts.le hv0)]
      have hvmod : IntMod.mk hV ⟨v, h.hyp125.pairFacts.le hv0⟩ ∈ modNull V₀ V hV := by
        rw [mem_modNull]
        exact hv0
      rw [show mkTil V₀ V hV (IntMod.mk hV ⟨v, h.hyp125.pairFacts.le hv0⟩) = 1 from
        (QuotientGroup.eq_one_iff (N := modNull V₀ V hV) _).2 hvmod]
      exact (wTil V₀ V hV L).one_mem
    have h1 : rk ↥Wt = mSub (wSub V₀ V hV L) - mSub V₀ := by
      have h := s15_Infra_mSub_eq_rk_imgTil_add V₀ V (wSub V₀ V hV L) hV
        (preTil_le V₀ V hV _)
      rw [show imgTil V₀ V hV (wSub V₀ V hV L) = Wt from by
        rw [hWt, wSub, imgTil_preTil], inf_eq_right.mpr hW0] at h
      omega
    have h2 : rk ↥U = mSub (v1Sub D.M V₀ V hV L ⊓ wSub V₀ V hV L) - mSub V₀ := by
      have h := s15_Infra_mSub_eq_rk_imgTil_add V₀ V
        (v1Sub D.M V₀ V hV L ⊓ wSub V₀ V hV L) hV
        (inf_le_right.trans (preTil_le V₀ V hV _))
      have h3 : (v1Sub D.M V₀ V hV L ⊓ wSub V₀ V hV L) ⊓ V₀ = V₀ := by
        rw [inf_assoc, inf_eq_right.mpr hW0]
        exact inf_eq_right.mpr (s15_Infra_le_v1Sub D.M V₀ V hV L)
      change mSub (v1Sub D.M V₀ V hV L ⊓ wSub V₀ V hV L) =
        rk ↥U + mSub ((v1Sub D.M V₀ V hV L ⊓ wSub V₀ V hV L) ⊓ V₀) at h
      rw [h3] at h
      omega
    rw [mQuot_eq_rk_sub hUW, h1, h2]
    have hW := mSub_wSub (V₀ := V₀) (V := V) (L := L) D h.hyp125 hV
    have hW' : mSub (wSub V₀ V hV L) =
        gamma15 D.M V₀ V hV L + mSub (v1Sub D.M V₀ V hV L ⊓ wSub V₀ V hV L) := by
      simpa only [delta15] using hW
    have hV0W : mSub V₀ ≤ mSub (wSub V₀ V hV L) := rk_mono hW0
    have hV0I : mSub V₀ ≤ mSub (v1Sub D.M V₀ V hV L ⊓ wSub V₀ V hV L) :=
      rk_mono (le_inf (s15_Infra_le_v1Sub D.M V₀ V hV L) hW0)
    have hsub : (mSub (wSub V₀ V hV L) - mSub V₀) -
        (mSub (v1Sub D.M V₀ V hV L ⊓ wSub V₀ V hV L) - mSub V₀) =
        mSub (wSub V₀ V hV L) -
          mSub (v1Sub D.M V₀ V hV L ⊓ wSub V₀ V hV L) := by omega
    rw [hsub, hW']
    omega
  have hmq : E3.mQuot B (B ⊓ U) + 1 ≤ gamma15 D.M V₀ V hV L := by
    have h1 : E3.mQuot (B ⊔ U) U + 1 ≤ E3.mQuot Wt U := by omega
    rw [← hWtU]
    rwa [hsplit] at h1
  have hBbound : rk ↥B ≤ gamma15 D.M V₀ V hV L := by
    have hinfle : rk ↥(B ⊓ U) ≤ rk ↥U := rk_mono inf_le_right
    rw [hBrank]
    omega
  exact hmbar.trans hBbound

theorem delta15_lt_of_quasisimple (hK : K_QuasisimpleFixHalf) (D : Data G)
    {V L : Subgroup G} (h : Hyp151 D ⊥ V L)
    (hq : CFSG.Open.IsQuasisimple ↥(barSub ⊥ V h.isElemAbelian L))
    (hKg : CFSG.Open.IsKGroup ↥(barSub ⊥ V h.isElemAbelian L))
    (hγ : 3 ≤ gamma15 D.M ⊥ V h.isElemAbelian L) :
    delta15 D.M ⊥ V h.isElemAbelian L < gamma15 D.M ⊥ V h.isElemAbelian L - 1 := by
  have hV := h.isElemAbelian
  let Lb : Subgroup (MulAut (Vtil ⊥ V hV)) := barSub ⊥ V hV L
  let U : Subgroup (Vtil ⊥ V hV) := wTil ⊥ V hV L
  have hUeq : CFSG.Quasithin.commSub U Lb = U := by
    simpa [Lb, U, wTil] using
      s15_Lin_commSub_commSub_eq_of_no_two_quotient (s15_Infra_vtil_sq_eq_one ⊥ V hV)
        (s15_Kbar_no_two_quotient h)
  have hStab : StableUnder Lb U := by
    intro x hx u hu
    exact CFSG.Quasithin.Asc81c.commSub_stable' hx (by simpa [U, wTil] using hu)
  have hKW := hK (Vtil ⊥ V hV) (s15_Infra_vtil_sq_eq_one ⊥ V hV) Lb hKg hq U hStab hUeq
  let I : Subgroup (Vtil ⊥ V hV) :=
    imgTil ⊥ V hV (v1Sub D.M ⊥ V hV L ⊓ wSub ⊥ V hV L)
  have hIleU : I ≤ U := by
    change imgTil ⊥ V hV (v1Sub D.M ⊥ V hV L ⊓ wSub ⊥ V hV L) ≤ wTil ⊥ V hV L
    have h := Subgroup.map_mono (f := (mkTil ⊥ V hV))
      (Subgroup.subgroupOf_mono V
        (inf_le_right : v1Sub D.M ⊥ V hV L ⊓ wSub ⊥ V hV L ≤ wSub ⊥ V hV L))
    change imgTil ⊥ V hV (v1Sub D.M ⊥ V hV L ⊓ wSub ⊥ V hV L) ≤
      imgTil ⊥ V hV (wSub ⊥ V hV L) at h
    rw [wSub, imgTil_preTil] at h
    exact h
  have hIleFix : I ≤ fixV Lb := by
    have h1 : imgTil ⊥ V hV (v1Sub D.M ⊥ V hV L) ≤ fixV (barSub ⊥ V hV L) := by
      simpa only [conjSubgroup_one] using
        s15_Core_imgTil_v1Sub_le_fixV h (m := (1 : G)) D.M.one_mem
    have h0 := Subgroup.map_mono (f := (mkTil ⊥ V hV))
      (Subgroup.subgroupOf_mono V
        (inf_le_left : v1Sub D.M ⊥ V hV L ⊓ wSub ⊥ V hV L ≤ v1Sub D.M ⊥ V hV L))
    change I ≤ imgTil ⊥ V hV (v1Sub D.M ⊥ V hV L) at h0
    exact h0.trans (by simpa [Lb] using h1)
  have hδle : delta15 D.M ⊥ V hV L ≤ rk ↥(U ⊓ fixV Lb) := by
    have hle : I ≤ U ⊓ fixV Lb := le_inf hIleU hIleFix
    have hrk : rk ↥I = delta15 D.M ⊥ V hV L := by
      have h := s15_Infra_mSub_eq_rk_imgTil_add ⊥ V
        (v1Sub D.M ⊥ V hV L ⊓ wSub ⊥ V hV L) hV
        (inf_le_right.trans (preTil_le ⊥ V hV _))
      have hzero : (v1Sub D.M ⊥ V hV L ⊓ wSub ⊥ V hV L) ⊓ ⊥ = ⊥ :=
        inf_eq_right.mpr bot_le
      rw [show imgTil ⊥ V hV (v1Sub D.M ⊥ V hV L ⊓ wSub ⊥ V hV L) = I from rfl,
        hzero] at h
      have hzero' : mSub (⊥ : Subgroup G) = 0 := by simp [mSub, rk]
      have h' : mSub (v1Sub D.M ⊥ V hV L ⊓ wSub ⊥ V hV L) = rk ↥I := by
        simpa [hzero'] using h
      rw [show delta15 D.M ⊥ V hV L =
        mSub (v1Sub D.M ⊥ V hV L ⊓ wSub ⊥ V hV L) from rfl]
      exact h'.symm
    rw [← hrk]
    exact rk_mono hle
  have h151 : Hyp151 D ⊥ V L := h
  have hUrank : rk ↥U = gamma15 D.M ⊥ V hV L + delta15 D.M ⊥ V hV L := by
    have h := s15_Infra_mSub_eq_rk_imgTil_add ⊥ V (wSub ⊥ V hV L) hV
      (preTil_le ⊥ V hV _)
    have himg : imgTil ⊥ V hV (wSub ⊥ V hV L) = U := by
      change imgTil ⊥ V hV (wSub ⊥ V hV L) = wTil ⊥ V hV L
      rw [wSub, imgTil_preTil]
    have hzero : wSub ⊥ V hV L ⊓ ⊥ = ⊥ := inf_eq_right.mpr bot_le
    rw [himg, hzero] at h
    have hW := mSub_wSub (V₀ := ⊥) (V := V) (L := L) D h151.hyp125 hV
    have hzero' : mSub (⊥ : Subgroup G) = 0 := by simp [mSub, rk]
    rw [hzero', add_zero] at h
    exact h.symm.trans hW
  have h2δ : 2 * delta15 D.M ⊥ V hV L ≤ gamma15 D.M ⊥ V hV L := by
    omega
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
