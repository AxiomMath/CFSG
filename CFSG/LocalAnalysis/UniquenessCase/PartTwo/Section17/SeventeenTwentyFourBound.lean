module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BBarSporadicTable
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.MBarSporadicTable
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SporadicNotClassical
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.J2Module12
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyNineProof
public import CFSG.GroupTheory.Fitting.QuasisimpleNormalFstarTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.List880Rank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsThreeThreeJ2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsElevenEight
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.J2QuadFourHolds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsThreeThreeJ2Holds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem irr_rank_twelve_of_caseTwo_J2
    {D : Data G} {V₀ V L : Subgroup G} (h : Hyp125 D V₀ V)
    (hL : L ∈ calC D.M) (hN : (L.subgroupOf D.M).Normal)
    (hne : barSub V₀ V h.isElemAbelian L ≠ ⊥)
    (hfix : fixV (barSub V₀ V h.isElemAbelian L) = ⊥)
    (hJ2 : IsSpor (BarInf L) .J2)
    (hsum : IsDirSumOver (conjSet (barSub V₀ V h.isElemAbelian L)
      (Mbar D.M V₀ V h.isElemAbelian))
      (fun X => commV (autQuot X (fixSupConjSet (barSub V₀ V h.isElemAbelian L)
        (Mbar D.M V₀ V h.isElemAbelian)))))
    {I : Subgroup (Vtil V₀ V h.isElemAbelian)}
    (hI : I ∈ irrSet (barSub V₀ V h.isElemAbelian L))
    (hmn : (E3.mParam (autSub (autQuot (Mbar D.M V₀ V h.isElemAbelian)
        (fixSupConjSet (barSub V₀ V h.isElemAbelian L) (Mbar D.M V₀ V h.isElemAbelian)))
        (I.map (QuotientGroup.mk' (fixSupConjSet (barSub V₀ V h.isElemAbelian L)
          (Mbar D.M V₀ V h.isElemAbelian))))) : ℚ) *
      ((rk ↥(commV (autQuot (barSub V₀ V h.isElemAbelian L)
        (fixSupConjSet (barSub V₀ V h.isElemAbelian L)
          (Mbar D.M V₀ V h.isElemAbelian)))) : ℚ) /
        (rk ↥(I.map (QuotientGroup.mk' (fixSupConjSet (barSub V₀ V h.isElemAbelian L)
          (Mbar D.M V₀ V h.isElemAbelian)))) : ℚ)) ≤
      mBar D.M V₀ V h.isElemAbelian)
    (hm7 : mBar D.M V₀ V h.isElemAbelian ≤ 7)
    (hrow : Inputs1719.W4Thm11_1Row .J2) (h118 : Inputs1719.W4Lem11_8Rk) :
    IsIrrOn (barSub V₀ V h.isElemAbelian L) ⊤ ⊥ ∧ rk (Vtil V₀ V h.isElemAbelian) = 12 := by
  classical
  have hV' := h.isElemAbelian
  have h4 := caseTwo_le_mParam h hL hne rfl rfl hsum hI hmn (MRowBound.of_row hrow hJ2)
  obtain ⟨heven, hmleN, hwit⟩ := caseTwo_package h hL hne rfl rfl hsum hI hmn
  set K := barSub V₀ V h.isElemAbelian L with hKdef
  set Mb := Mbar D.M V₀ V h.isElemAbelian with hMbdef
  set Z := fixSupConjSet K Mb with hZdef
  simp only [Inputs1719.tableM] at h4
  obtain ⟨s₀, hs₀, hs₀o, hs₀rk⟩ :=
    CFSG.Quasithin.E3.exists_involution_rkIdx_fixV_eq_mParam _ heven
  obtain ⟨W, _, _, Y, X, hW, hXY, hXN, -, hXq, -, hoddX, ⟨eX⟩, hXirr, hmY, hrkW⟩ :=
    hwit s₀ hs₀ hs₀o
  have hXJ2 : IsSpor ↥X .J2 := by
    obtain ⟨f⟩ := hJ2
    exact PartTwo.isSpor_J2_of_odd_center hXq hoddX ⟨eX.trans f⟩
  have hmY8 : E3.mParam Y < 8 := by
    have := hmY.trans (le_of_eq hs₀rk)
    omega
  have hrk12 : rk W = 12 := h118 W hW Y X hXY hXN hXJ2 hXirr hmY8
  have hIstar12 : rk ↥(I.map (QuotientGroup.mk' Z)) = 12 := (hrkW hfix).symm.trans hrk12
  have hLM : L ≤ D.M := hL.1.le
  have hKM : K ≤ Mb := barSub_mono V₀ V hV' hLM
  have hMN : Mb ≤ Subgroup.normalizer (K : Set (MulAut (Vtil V₀ V h.isElemAbelian))) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).1
      (barSub_subgroupOf_mbar_normal hV' hLM
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hLM).1 hN))
  have hconj : conjSet K Mb = {K} := by
    ext Y'
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact Set.mem_singleton_iff.mpr (Subgroup.mem_normalizer_iff_map_conj_eq.1 (hMN hm))
    · intro hY'
      rw [Set.mem_singleton_iff] at hY'
      subst hY'
      exact ⟨1, Mb.one_mem, by ext x; simp [MulAut.conj_apply]⟩
  have hsup : supConjSet K Mb = K := by
    simp only [supConjSet, hconj, Set.mem_singleton_iff, iSup_iSup_eq_left]
  have hZbot : Z = ⊥ := by
    rw [hZdef]
    show fixV (supConjSet K Mb) = ⊥
    rw [hsup]
    exact hfix
  have hKZ : K ≤ stabSub Z := by
    rw [hZdef]
    exact hsup.ge.trans (CFSG.Quasithin.RonanF918.le_stabSub_fixV _)
  have hπinj : Function.Injective (QuotientGroup.mk' Z) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
    exact hZbot
  have htop : commV (autQuot K Z) = ⊤ := by
    have h2' : (⨆ X ∈ conjSet K Mb, commV (autQuot X Z)) = ⊤ := by
      rw [iSup_subtype' (p := fun X : Subgroup (MulAut (Vtil V₀ V h.isElemAbelian)) =>
        X ∈ conjSet K Mb) (f := fun X _ => commV (autQuot X Z))]
      exact hsum.2
    rw [hconj] at h2'
    simpa using h2'
  have hcommK : commV K = ⊤ := by
    have h3 : (commV K).map (QuotientGroup.mk' Z) =
        (⊤ : Subgroup (Vtil V₀ V h.isElemAbelian)).map (QuotientGroup.mk' Z) := by
      rw [map_commV_eq_commV_autQuot K Z hKZ, htop,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective Z)]
    exact Subgroup.map_injective hπinj h3
  have hrkcomm : rk ↥(commV (autQuot K Z)) = rk (Vtil V₀ V h.isElemAbelian) := by
    rw [← map_commV_eq_commV_autQuot K Z hKZ, hcommK]
    unfold rk
    rw [Subgroup.card_map_of_injective hπinj, Subgroup.card_top]
  have hIrk : rk ↥I = 12 := by
    rw [← hIstar12]
    unfold rk
    rw [Subgroup.card_map_of_injective hπinj]
  have hVle : rk (Vtil V₀ V h.isElemAbelian) ≤ 21 := by
    have hq := hmn
    rw [hrkcomm, hIstar12] at hq
    have h4q : (4 : ℚ) ≤ (E3.mParam (autSub (autQuot Mb Z)
        (I.map (QuotientGroup.mk' Z))) : ℚ) := by exact_mod_cast h4
    have h7q : (mBar D.M V₀ V h.isElemAbelian : ℚ) ≤ 7 := by exact_mod_cast hm7
    have hnn : (0 : ℚ) ≤ (rk (Vtil V₀ V h.isElemAbelian) : ℚ) / ((12 : ℕ) : ℚ) := by
      positivity
    have h5 : (4 : ℚ) * ((rk (Vtil V₀ V h.isElemAbelian) : ℚ) / ((12 : ℕ) : ℚ)) ≤ 7 :=
      le_trans (mul_le_mul_of_nonneg_right h4q hnn) (hq.trans h7q)
    have h6 : (rk (Vtil V₀ V h.isElemAbelian) : ℚ) ≤ 21 := by
      push_cast at h5
      linarith
    exact_mod_cast h6
  have hKJ2 : IsSpor ↥K .J2 := by
    obtain ⟨f⟩ := hJ2
    exact PartTwo.isSpor_J2_of_odd_center (barSub_mem_compBar_of_ne_bot h hL hne).2.2
      (odd_center_barSub h hL hne)
      ⟨(Classical.choice
        (barSub_centerQuot_equiv_barInf (V₀ := V₀) (V := V) h hL hne)).symm.trans f⟩
  have hd := PartTwo.twelve_le_dMinDeg_of_isSpor_J2 hKJ2
  have hIst : StableUnder K I := hI.2.2.1
  have hKstab : K ≤ stabSub I :=
    CFSG.Quasithin.B1.le_stabSub_of_invariant (fun g hg w hw => hIst g hg w hw)
  have hUexp : ∀ u : Vtil V₀ V h.isElemAbelian ⧸ I, u ^ 2 = 1 := by
    intro u
    induction u using QuotientGroup.induction_on with
    | H y => rw [← QuotientGroup.mk_pow, s15_Infra_vtil_sq_eq_one V₀ V hV' y, QuotientGroup.mk_one]
  let ρ : ↥K →* MulAut (Vtil V₀ V h.isElemAbelian ⧸ I) :=
    (quotHom I).comp (Subgroup.inclusion hKstab)
  have hquot : rk (Vtil V₀ V h.isElemAbelian ⧸ I) = rkIdx I := rfl
  have hlt : rk (Vtil V₀ V h.isElemAbelian ⧸ I) < dMinDeg ↥K := by
    have := rk_add_rkIdx I
    omega
  have hρ : ρ = 1 := PartTwo.eq_one_of_rk_lt_dMinDeg hUexp ρ hlt
  have hcommI : commSub ⊤ K ≤ I := by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨k, hk, v, -, rfl⟩
    have h1' : ρ ⟨k, hk⟩ = 1 := by rw [hρ]; rfl
    have h2' : (QuotientGroup.mk (k v) : Vtil V₀ V h.isElemAbelian ⧸ I) =
        QuotientGroup.mk v := by
      have := congrArg (fun f : MulAut (Vtil V₀ V h.isElemAbelian ⧸ I) =>
        f (QuotientGroup.mk v)) h1'
      simpa [ρ, quotHom_mk] using this
    exact (CFSG.Quasithin.mk_eq_mk_iff (k v) v).1 h2'
  have hItop : I = ⊤ := by
    rw [eq_top_iff, ← hcommK, CFSG.Quasithin.commV_eq_commSub]
    exact hcommI
  have hirr : IsIrrOn K ⊤ ⊥ := by
    have h' := hI.2
    rwa [hItop, hfix, inf_bot_eq] at h'
  refine ⟨hirr, ?_⟩
  rw [← hIrk, hItop]
  unfold rk
  rw [Subgroup.card_top]

theorem fstar_barSub_sup_T_eq {D : Data G} {V₀ V L : Subgroup G} (h : Hyp125 D V₀ V)
    (hL : L ∈ calC D.M) (hN : (L.subgroupOf D.M).Normal)
    (hq : CFSG.IsQuasisimple ↥(barSub V₀ V h.isElemAbelian L))
    (hirr : IsIrrOn (barSub V₀ V h.isElemAbelian L) ⊤ ⊥) :
    Fstar (barSub V₀ V h.isElemAbelian L ⊔ barSub V₀ V h.isElemAbelian D.T) =
      barSub V₀ V h.isElemAbelian L := by
  have hV' := h.isElemAbelian
  have hLM : L ≤ D.M := hL.1.le
  have hsq : ∀ w : Vtil V₀ V h.isElemAbelian, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV'
  have hmul : ∀ w : Vtil V₀ V h.isElemAbelian, w * w = 1 :=
    fun w => by simpa [pow_two] using hsq w
  have hntW : Nontrivial (Vtil V₀ V h.isElemAbelian) := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    have hbot : (⊥ : Subgroup (Vtil V₀ V h.isElemAbelian)) = ⊤ := by
      ext x
      rw [Subgroup.mem_bot]
      exact ⟨fun _ => Subgroup.mem_top x, fun _ => Subsingleton.elim x 1⟩
    exact (ne_of_lt hirr.1) hbot
  have hirrR : CFSG.LocalAnalysis.RankThreeUC.IsIrrOn (barSub V₀ V h.isElemAbelian L) :=
    fun U hU => hirr.2.2.2 U hU bot_le le_top
  have hT : CFSG.Quasithin.IsSylowIn 2 (barSub V₀ V h.isElemAbelian D.T)
      (Mbar D.M V₀ V h.isElemAbelian) :=
    isSylowIn_barSub_sylow D hV'
      (le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀)
  exact fstar_eq_of_generalizedFitting_eq le_sup_left
    (CFSG.GroupTheory.generalizedFitting_sup_eq_of_isPGroup_two_of_isIrrOn
      (W := Vtil V₀ V h.isElemAbelian) hmul hq (barSub_mono V₀ V hV' hLM) hT.1 hirrR
      (normal_barSub_of_normal hV' hLM hN) hT.2.1)

theorem mBar_le_four_and_aBar_eq_two
    {D : Data G} {V₀ V L : Subgroup G} (h : Hyp125 D V₀ V)
    (hL : L ∈ calC D.M) (hN : (L.subgroupOf D.M).Normal)
    (hne : barSub V₀ V h.isElemAbelian L ≠ ⊥)
    (hJ2 : IsSpor ↥(barSub V₀ V h.isElemAbelian L) .J2)
    (hirr : IsIrrOn (barSub V₀ V h.isElemAbelian L) ⊤ ⊥)
    (hrk : rk (Vtil V₀ V h.isElemAbelian) = 12)
    (h33 : Inputs1719.W4Lem3_3J2) (hKQ : Inputs1719.K_J2QuadFour) :
    mBar D.M V₀ V h.isElemAbelian ≤ 4 ∧ aBar D.M V₀ V h.isElemAbelian = 2 := by
  classical
  have hV' := h.isElemAbelian
  have hLM : L ≤ D.M := hL.1.le
  have hsq : ∀ w : Vtil V₀ V h.isElemAbelian, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV'
  have hKcomp := barSub_mem_compBar_of_ne_bot h hL hne
  have hqO : CFSG.Open.IsQuasisimple ↥(barSub V₀ V h.isElemAbelian L) := hKcomp.2.2
  have hq : CFSG.IsQuasisimple ↥(barSub V₀ V h.isElemAbelian L) :=
    CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hqO
  have hLMb : barSub V₀ V hV' L ≤ Mbar D.M V₀ V hV' := barSub_mono V₀ V hV' hLM
  have hT : CFSG.Quasithin.IsSylowIn 2 (barSub V₀ V h.isElemAbelian D.T)
      (Mbar D.M V₀ V h.isElemAbelian) :=
    isSylowIn_barSub_sylow D hV'
      (le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀)
  let Y : Subgroup (MulAut (Vtil V₀ V h.isElemAbelian)) :=
    barSub V₀ V hV' L ⊔ barSub V₀ V hV' D.T
  have hYle : Y ≤ Mbar D.M V₀ V hV' := sup_le hLMb hT.1
  have hXnorm : ((barSub V₀ V hV' L).subgroupOf (Mbar D.M V₀ V hV')).Normal :=
    normal_barSub_of_normal hV' hLM hN
  have hYnorm : ((barSub V₀ V hV' L).subgroupOf Y).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (hYle.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hLMb).mp hXnorm))
  have hF : Fstar Y = barSub V₀ V hV' L := fstar_barSub_sup_T_eq h hL hN hq hirr
  obtain ⟨⟨z, hzL, hzo, hz4⟩, ha2⟩ :=
    h33 _ hsq Y (barSub V₀ V hV' L) le_sup_left hYnorm hF hJ2 hirr hrk
  refine ⟨?_, ?_⟩
  ·
    have hm := CFSG.Quasithin.Asc81c.Pf.mParam_le_of_orderOf_two (hLMb hzL) hzo
    rw [rkIdx_fixV_zpowers, CFSG.Quasithin.commV_eq_commSub, hz4] at hm
    exact hm
  · refine le_antisymm ?_ ?_
    ·
      exact (PartTwo.aParam_le_of_isSylowIn_le hT le_sup_right).trans ha2
    ·
      obtain ⟨A, hA⟩ := hKQ _ hsq (barSub V₀ V hV' L) hJ2 hirr hrk
      exact E3.le_aParam_of_mem_aSet (by norm_num) (mem_aSet_of_le hA (hA.1.trans hLMb))

section OrderCertificates


theorem b17_24Bound_holds
    (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D)
    (h4128 : W4Lem12_8) (h869 : F08.R869 D) (h117 : C117 D V₀ V)
    (h640 : UC6.R6_40_2 D) (hFF : W4Thm12McClurg) (h77 : Inputs1719.W4Lem7_7)
    (hrow : Inputs1719.W4Thm11_1Row .J2) (h118 : Inputs1719.W4Lem11_8Rk)
    (h33 : Inputs1719.W4Lem3_3J2) (hKQ : Inputs1719.K_J2QuadFour) : B17_24Bound D V₀ V hV := by
  intro L hL hN hJ2
  have hV' := hV.isElemAbelian
  have hsimple : IsSimpleGroup (Bar2 L) := by
    obtain ⟨e⟩ := hJ2
    exact e.isSimpleGroup_congr.mpr CFSG.Sporadic.J2.isSimpleGroup_J2
  have hs : IsSpor (BarInf L) .J2 :=
    isSpor_barInf_of_isSpor_bar2 hL CFSG.Sporadic.J2.isSimpleGroup_J2 hJ2
  have hnt : ¬ F08.Thin8 L :=
    not_thin8_of_two_le_pRank Nat.prime_three (by norm_num)
      (two_le_pRank_of_bar2 Nat.prime_three (by norm_num) (two_le_pRank_three_of_isSpor_J2 hJ2))
  have hne := barSub_ne_bot_of_not_thin hV h117 hL hnt
  have hfix := fixV_barSub_eq_bot_of_not_classical D h869 h127 h640 hFF hV hL hN hnt
    (not_classicalEvenAltG2Der_of_isSpor_J2 hJ2)
  have hb : bBar L D.M V₀ V hV' ≤ 3 := by
    have := bBar_le_tableA_of_normal hV h77 hrow hL hN hs
    simpa only [Inputs1719.tableA] using this
  by_cases hm : 7 < mBar D.M V₀ V hV'
  · exact Or.inl ⟨(hV.mBarGT_iff_lt_mBar 7).2 hm, hb⟩
  · right
    have hm7 : mBar D.M V₀ V hV' ≤ 7 := by omega
    have hLstab : L ≤ stabTil V₀ V :=
      hL.1.le.trans (le_stabTil hV.pairFacts.le_normalizer hV.pairFacts.le_normalizer₀)
    have h2 : barSub V₀ V hV' (pCoreOf 2 L) = ⊥ :=
      TwelveTwentyThree.barSub_pCoreOf_eq_bot_of_isSubnormal hV' hL.1
        (barSub_pCoreOf_eq_bot_of_hyp125 hV)
    obtain ⟨e⟩ := nonempty_bar2_mulEquiv_barSub_of_isSimpleGroup hV' hLstab h2 hne hsimple
    have hJ2bar : IsSpor ↥(barSub V₀ V hV' L) .J2 := by
      obtain ⟨f⟩ := hJ2
      exact ⟨e.symm.trans f⟩
    have hKcomp : barSub V₀ V hV' L ∈ compBar D.M V₀ V hV' :=
      barSub_mem_compBar_of_ne_bot hV hL hne
    have hm4 : 4 ≤ mBar D.M V₀ V hV' := by
      have := tableM_le_mBar D hx h61 h127 h1214 h4128 hV hL hne hrow.rowM hs
        (not_lieModel_psl_two_of_isSpor_J2 hs)
      simpa only [Inputs1719.tableM] using this
    rcases twelve_twentyFour D hx h61 h127 h1214 h4128 hV hKcomp rfl with
      h1 | ⟨hsum, I, hI, hmn⟩ | ⟨Y, e', -, -, hsn, hnat, -⟩
    · have := twelve_le_dMinDeg_of_isSpor_J2 hJ2bar
      omega
    · obtain ⟨hirr, hrk⟩ := irr_rank_twelve_of_caseTwo_J2 hV hL hN hne hfix hs hsum hI hmn hm7
        hrow h118
      obtain ⟨hle4, ha2⟩ :=
        mBar_le_four_and_aBar_eq_two hV hL hN hne hJ2bar hirr hrk h33 hKQ
      exact ⟨hirr, hrk, le_antisymm hle4 hm4, ha2⟩
    · exact (not_lieModel_psl_two_of_isSpor_J2 hs e'
        (lieModel_psl_two_of_isNaturalO4Plus hV hL hne hsn hnat)).elim

theorem seventeen_twentyfour_holds
    (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V)
    (h17_20 : R17_20At D V₀ V) (h17_23 : R17_23At D V₀ V)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D)
    (h4128 : W4Lem12_8) (h869 : F08.R869 D) (h117 : C117 D V₀ V)
    (h640 : UC6.R6_40_2 D) (hFF : W4Thm12McClurg) (h77 : Inputs1719.W4Lem7_7)
    (hrow : Inputs1719.W4Thm11_1Row .J2) (h118 : Inputs1719.W4Lem11_8Rk) :
    R17_24At D V₀ V :=
  seventeen_twentyfour D V₀ V hV h17_20 h17_23
    (b17_24Bound_holds D V₀ V hV hx h61 h127 h1214 h4128 h869 h117 h640 hFF h77
      hrow h118 Inputs1719.w4Lem3_3J2_holds Inputs1719.k_J2QuadFour_holds)

end OrderCertificates

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
