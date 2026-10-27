module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.DeltaPrimePullback
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenNine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusTwoAset
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OmegaMinusThreeNatHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OmegaMinusFourThreeNatHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OmegaSixMinusL2FixFree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U4DeltaHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.L2SzAutRankHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U4BorelQuotientHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SU44TwoNatHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1FbSyl
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16Opp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenNineAParam
public import CFSG.LocalAnalysis.WeakClosure81.DeltaPairWC
public import CFSG.LocalAnalysis.WeakClosure81.FixFreeClosure
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenThirteenH1Holds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.WeakClosure81 (InFSq InCalU wc_of_delta_pair fixFree_closure_facts)
open Inputs1719 (K_O6m4_L2FixFree fixV_eq_bot_of_sumOfNat_omegaMinus)

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_wClos_of_fixFree (hKL2 : Inputs1719.K_L2SzAutRank)
    {V T J X₁ : Subgroup G} (hV : IsElemAbelian 2 V) (hV1 : V ≠ ⊥) (hVT : V ≤ T)
    (hX₁V : X₁ ≤ normalizer (V : Set G)) (hT : IsSylowIn 2 T X₁) (hJX : J ≤ X₁)
    (hXJ : X₁ ≤ normalizer (J : Set G)) (hX₁ : X₁ = T ⊔ J) {m : ℕ}
    (hL2 : IsL2 (Bar2 J) m) (hfix : V ⊓ centralizer (J : Set G) = ⊥) {i : ℕ}
    (hi : i + m < E3.sParam hV) : X₁ ≤ normalizer (E3.wClos V i T : Set G) := by
  set U := CFSG.Quasithin.conjClosure (V ⊓ centralizer (T : Set G)) X₁ with hUdef
  obtain ⟨-, hUV, hXU, hJC, hKT⟩ := fixFree_closure_facts hV1 hVT hX₁V hT hJX hXJ hX₁
    (CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL2) hfix hUdef
  have hU : IsElemAbelian 2 U := CFSG.Open.IsElemAbelian.mono hV hUV
  have ha := aParam_autI_le_of_fixFree hKL2 hU hUdef hT hJX hXJ hX₁ hXU hJC hKT hL2
  have hi' : i < E3.sParam hV - E3.aParam (autI hU X₁) := by omega
  have hTN : T ≤ normalizer (E3.wClos V i T : Set G) :=
    Subgroup.le_normalizer.trans (E3.normalizer_le_normalizer_wClos T)
  intro x hx
  obtain ⟨c, hc, n, hn, rfl⟩ := E3.e3_18_factor hV hT hXU hU hi' x hx
  exact Subgroup.mul_mem _ (hTN (hKT hc)) hn.2

theorem isL2_bar2_barSub_of_le {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) {L J : Subgroup G}
    (hLS : L ≤ stabTil V₀ V)
    (hker : ∀ x (hxL : x ∈ L), actTil V₀ V hV ⟨x, hLS hxL⟩ = 1 → x ∈ pCoreOf 2 L)
    (hJL : J ≤ L) {n : ℕ} (hJ : IsL2 (Bar2 J) n) : IsL2 (Bar2 (barSub V₀ V hV J)) n := by
  classical
  let ψ : ↥J →* ↥(barSub V₀ V hV J) :=
    ((actTil V₀ V hV).comp (Subgroup.inclusion (hJL.trans hLS))).codRestrict (barSub V₀ V hV J)
      (fun x => actTil_mem_barSub V₀ V hV x.2 ((hJL.trans hLS) x.2))
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨a, haJ, hay⟩ := (mem_barSub V₀ V hV J (y : MulAut (Vtil V₀ V hV))).1 y.2
    exact ⟨⟨a, haJ⟩, Subtype.ext hay⟩
  have hψker : IsPGroup 2 ψ.ker := by
    have h2 : IsPGroup 2 ((pCoreOf 2 L).comap J.subtype) :=
      IsPGroup.comap_of_injective (UC22.uc22p21c_isPGroup_pCoreOf L) J.subtype
        J.subtype_injective
    refine h2.to_le fun k hk => ?_
    have hk1 : actTil V₀ V hV ⟨(k : G), hLS (hJL k.2)⟩ = 1 := congrArg Subtype.val hk
    exact hker _ (hJL k.2) hk1
  obtain ⟨e⟩ := CFSG.nonempty_quotient_pCore_equiv_of_surjective_of_isPGroup_ker ψ hψ hψker
  exact CFSG.Blueprint.LieModel.of_mulEquiv e hJ

theorem isL2_bar2_of_barImage {X J : Subgroup G} (hJX : J ≤ X) {n : ℕ}
    (h : IsL2 (Bar2 (UC22.barImage X J)) n) : IsL2 (Bar2 J) n := by
  classical
  obtain ⟨e⟩ := bar2_mulEquiv_map_of_isPGroup_ker (QuotientGroup.mk' (CFSG.pCore 2 ↥X))
    (by rw [QuotientGroup.ker_mk']; exact CFSG.pCore_isPGroup) (J.subgroupOf X)
  have e2 : Bar2 (J.subgroupOf X) ≃* Bar2 J :=
    UC6S846.bar2Equiv (Subgroup.subgroupOfEquivOfLe hJX)
  exact CFSG.Blueprint.LieModel.of_mulEquiv (e.symm.trans e2) h

section Certified


theorem gap_18_9_WC_holds {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h61 : CFSG.LocalAnalysis.UniquenessCase.UC6.R6_1 D) (h111 : W3Thm111 G)
    (h1742 : S17.R17_42At D V₀ V) (hKU4 : Inputs1719.KU4Delta)
    (hKL2 : Inputs1719.K_L2SzAutRank) (hKM : Inputs1719.K_O6m4_ThreeNatM)
    (hKfix : K_O6m4_L2FixFree) (h : Hyp18 D V₀ V p L) :
    Gap_18_9_WC D V₀ V p L h := by
  classical
  intro hV₀ hO hS
  subst hV₀
  have hV : IsElemAbelian 2 V := h.hyp125.isElemAbelian
  have hU4bar : IsU4 ↥(barSub ⊥ V hV (UC22.conjClosure D.M L)) 2 := isU4_of_isOmegaMinus hO
  obtain ⟨hXL, -, -, hcong⟩ := isU4_barSub_cong h h1742 hU4bar
  have hpq : p ∣ 2 ^ 2 + 1 := by
    have h5 : (p : ℤ) ∣ 2 ^ 2 + 1 := by simpa using hcong.symm.dvd
    exact Int.natCast_dvd_natCast.mp h5
  have hsbar : IsSimpleGroup ↥(barSub ⊥ V hV (UC22.conjClosure D.M L)) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU4bar
  have hX1 : barSub ⊥ V hV (UC22.conjClosure D.M L) ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot _).1 hsbar.toNontrivial
  obtain ⟨-, ⟨e⟩⟩ := conjClosure_eq_and_bar2_equiv_of_hyp18 h hsbar
  have hU4 : IsU4 (Bar2 (UC22.conjClosure D.M L)) 2 := by
    have h1 : IsU4 ↥(barSub ⊥ V hV L) 2 := by rw [← hXL]; exact hU4bar
    rw [hXL]
    exact CFSG.Blueprint.LieModel.of_mulEquiv e.symm h1
  have hsX : IsSimpleGroup (Bar2 (UC22.conjClosure D.M L)) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU4
  obtain ⟨P, Y₀, P₁, J₁, X₁, N, H, hP₁, hJ₁, hX₁, hH, hNX, hY₀N, -, hTX₁, hX₁M, hTH, hHM,
    hcardH, -, -, hN₀J₁, hJL2, hTP₁, hTXJ, hbJ, ⟨E₀, hE₀le, hE₀el, hE₀card⟩⟩ :=
    u4_X1_data h hKU4 hKL2 (le_refl 2) hU4 hpq
  have hP₁X : P₁ ≤ UC22.conjClosure D.M L := hP₁ ▸ uc22p21c_barPreimage_le _ P
  have hJ₁P₁ : J₁ ≤ P₁ := hJ₁ ▸ CFSG.LocalAnalysis.RankThreeUC.pElementSubgroup_le 2 P₁
  have hJ₁X : J₁ ≤ UC22.conjClosure D.M L := hJ₁P₁.trans hP₁X
  obtain ⟨A', hA'el, hA'card⟩ :=
    u4_noncyclic (X := UC22.conjClosure D.M L) (P := P) (Y₀ := Y₀) (P₁ := P₁) (J₁ := J₁)
      (N := N) (E := E₀) h.p_prime h.p_ne_two hP₁ hJ₁ hY₀N hP₁X hNX hJ₁P₁ hN₀J₁ hE₀le hE₀el
      hE₀card
  let A : Subgroup G := A'.map (J₁ ⊔ N).subtype
  have hAel : CFSG.Open.IsElemAbelian p A := hA'el.map (J₁ ⊔ N).subtype
  have hAcard : Nat.card A = p ^ 2 := by
    rw [Subgroup.card_map_of_injective (J₁ ⊔ N).subtype_injective, hA'card]
  have hAX : A ≤ X₁ ⊔ H :=
    (Subgroup.map_subtype_le A').trans
      (sup_le_sup (hX₁ ▸ le_sup_right) (hH ▸ le_sup_right))
  have hAc : ¬ IsCyclic A := UC22.uc22p22u_not_isCyclic_of_card_sq h.p_prime hAel hAcard
  have hsup : (⨆ K ∈ ({X₁ ⊔ H} : Set (Subgroup G)), K) = X₁ ⊔ H := by simp
  have hU : CFSG.LocalAnalysis.WeakClosure81.InCalU D.M (X₁ ⊔ H) := by
    have h1 := uniqueMax_iSup_of_noncyclic_of_le D h61 h (Δ := {X₁ ⊔ H})
      (hsup.le.trans (sup_le hX₁M hHM)) (by rw [hsup]; exact ⟨D.maxLocal, sup_le hX₁M hHM⟩)
      (hAX.trans hsup.symm.le) hAel.isPGroup hAc
    rw [hsup] at h1
    exact h1
  have hXS : UC22.conjClosure D.M L ≤ stabTil ⊥ V :=
    h.X_le_M.trans (le_stabTil h.hyp125.pairFacts.le_normalizer
      (by rw [Subgroup.normalizer_eq_top]; exact le_top))
  have hXn : ((UC22.conjClosure D.M L).subgroupOf D.M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.X_le_M).2
      (TwelveTwentyThree.le_normalizer_conjClosure D.M L)
  have hXsub : CFSG.Open.IsSubnormal (UC22.conjClosure D.M L) D.M :=
    CFSG.Open.IsSubnormal.step h.X_le_M hXn (CFSG.Open.IsSubnormal.refl D.M)
  have hJL2' : IsL2 (Bar2 J₁) 2 := isL2_bar2_of_barImage hJ₁X (hbJ ▸ hJL2)
  have hJbarL2 : IsL2 (Bar2 (barSub ⊥ V hV J₁)) 2 :=
    isL2_bar2_barSub_of_le hV hXS
      (fun x hx hact => CFSG.LocalAnalysis.UniquenessCase.PartTwo.mem_pCoreOf_of_actTil_eq_one
        h.hyp125 hXsub hsX hX1 hx (hXS hx) hact) hJ₁X hJL2'
  obtain ⟨-, -, -, -, hTXsyl, -⟩ := tPullbackData h (X := UC22.conjClosure D.M L) rfl
  have hSyl : IsSylowIn 2 (barSub ⊥ V hV (D.T ⊓ UC22.conjClosure D.M L))
      (barSub ⊥ V hV (UC22.conjClosure D.M L)) := s16c1_barSub_sylow hXS hTXsyl
  have hfixbar : fixV (barSub ⊥ V hV J₁) = ⊥ :=
    fixV_eq_bot_of_sumOfNat_omegaMinus hKfix (s15_Infra_vtil_sq_eq_one ⊥ V hV) hO hS hSyl
      (barSub_mono ⊥ V hV hTXJ) (barSub_mono ⊥ V hV hJ₁X) hJbarL2
  have hfix : V ⊓ centralizer (J₁ : Set G) = ⊥ := by
    rw [← WeakClosure81.preCTilde_bot_eq hV (hJ₁X.trans hXS), WeakClosure81.preCTilde, hfixbar,
      preTil_bot, inf_bot_eq]
  have h6 : 6 ≤ CFSG.Quasithin.E3.mParam (Mbar D.M ⊥ V hV) :=
    hKM (Vtil ⊥ V hV) (s15_Infra_vtil_sq_eq_one ⊥ V hV)
      (barSub ⊥ V hV (UC22.conjClosure D.M L)) (Mbar D.M ⊥ V hV) (barSub_mono ⊥ V hV h.X_le_M)
      (Mbar_le_normalizer_barSub_conjClosure h) hO hS
  have hmbar : 6 ≤ mBar D.M ⊥ V hV := h6
  have hV1' : InCalV1 D.M D.T V := by
    rcases h.hyp125.1 with ⟨hW, -⟩ | ⟨h0, -⟩
    · exact hW.1.1
    · exact absurd rfl h0.1.1
  have hm2 : MBarGT D.M ⊥ V 2 := (h.hyp125.mBarGT_iff_lt_mBar 2).2 (by omega)
  have hm5 : MBarGT D.M ⊥ V 5 := (h.hyp125.mBarGT_iff_lt_mBar 5).2 (by omega)
  have hs : 5 < E3.sParam hV := TwelveShort.lt_sParam_of_mBarGT D h111 hV1' hm2 hm5
  have hrk : 3 < CFSG.Quasithin.rk ↥V := by
    have h1 : mBar D.M ⊥ V hV ≤ CFSG.Quasithin.rk ↥V :=
      CFSG.LocalAnalysis.WeakClosure81.mBar_le_rk (M := D.M) hV bot_le
    omega
  have hT2 : IsPGroup 2 D.T :=
    (CFSG.LocalAnalysis.WeakClosure81.isSylowOf_two_iff_isSylowIn.mp D.sylowG).2.1
  have hX₁J : X₁ ≤ normalizer (J₁ : Set G) := by
    rw [hX₁]
    refine sup_le (fun t ht => ?_) Subgroup.le_normalizer
    rw [hJ₁]
    exact close16_mem_normalizer_opp 2 (hTP₁ ht)
  have hW3 : X₁ ≤ normalizer (E3.wClos V 3 D.T : Set G) :=
    le_normalizer_wClos_of_fixFree hKL2 hV h.hyp125.inCalV.1 (s15_13A_le_T h.hyp125)
      (hX₁M.trans h.hyp125.pairFacts.le_normalizer) (TwelveShort.isSylowIn_of_le D hTX₁)
      (hX₁ ▸ le_sup_right) hX₁J hX₁ hJL2' hfix (by omega)
  have hk : D.k ≤ 2 := TwelveSeven.k_le_two D
  exact wc_of_delta_pair hV D.maxLocal hT2
    (TwelveShort.wClos_zero_ne_bot D h.hyp125.inCalV) h.p_prime h.p_ne_two (by omega) hX₁M hTH
    hHM hcardH hU (by omega : D.k + 1 ≤ 3) hrk hW3

theorem eighteen_nine_holds {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (hx : DataExt D) (h61 : CFSG.LocalAnalysis.UniquenessCase.UC6.R6_1 D) (h127 : R127 D)
    (h126 : R126 D) (h111 : W3Thm111 G)
    (h1742 : S17.R17_42At D V₀ V) (h641 : S17.R17_64_1At D V₀ V)
    (h642 : S17.R17_64_2At D V₀ V) (h643 : S17.R17_64_3At D V₀ V)
    (h171 : ∀ hV : Hyp125 D V₀ V, S17.R17_1At D V₀ V hV)
    (h8103 : F08.R8103 D) (h8106 : F08.R8106 D)
    (hKfix : Inputs1719.K_O6m4_L2FixFree)
    (h : Hyp18 D V₀ V p L) :
    R18_9At D V₀ V p L h := by
  have hKU4 : Inputs1719.KU4Delta := Inputs1719.kU4Delta_holds
  exact eighteen_nine hx h61 h127 h126 h111 h1742 h641 h642 h643 h171
    Inputs1719.kU4U5CartanQuotient_holds h8103 h8106 Inputs1719.k_O4m4_ThreeNat_holds
    Inputs1719.k_O6m4_ThreeNatM_holds h
    (gap_18_9_WC_holds h61 h111 h1742 hKU4 Inputs1719.k_L2SzAutRank_holds
      Inputs1719.k_O6m4_ThreeNatM_holds hKfix h)

theorem eighteen_thirteen_holds {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (hm : MBarGT D.M V₀ V 3)
    (h6b : R18_6bAt D V₀ V p L h) (h7b : R18_7bAt D V₀ V p L h)
    (h8 : R18_8At D V₀ V p L h)
    (h10 : R18_10At D V₀ V p L h) (h11 : R18_11At D V₀ V p L h)
    (h12 : R18_12At D V₀ V p L h)
    (h17_66_1 : S17.R17_66_1At D V₀ V) (h18_4 : R18_4At D V₀ V p L)
    (h117 : C117 D V₀ V)
    (hx : DataExt D) (h61 : CFSG.LocalAnalysis.UniquenessCase.UC6.R6_1 D) (h127 : R127 D)
    (h1214 : F12.R1214 D)
    (h1742 : S17.R17_42At D V₀ V)
    (h126 : R126 D) (h111 : W3Thm111 G)
    (h171 : ∀ hV : Hyp125 D V₀ V, S17.R17_1At D V₀ V hV)
    (h8103 : F08.R8103 D) (h8106 : F08.R8106 D)
    (h641 : S17.R17_64_1At D V₀ V) (h642 : S17.R17_64_2At D V₀ V)
    (h643 : S17.R17_64_3At D V₀ V)
    (hKfix : Inputs1719.K_O6m4_L2FixFree) :
    R18_13At D V₀ V p L h := by
  have hKU4 : Inputs1719.KU4Delta := Inputs1719.kU4Delta_holds
  exact eighteen_thirteen_d h hm h6b h7b h8 h10 h11 h12 h17_66_1 h18_4 h117
    k_K_18_13_H1_holds hx h61 h127 h1214
    h1742 h126 h111 h171 Inputs1719.kU4U5CartanQuotient_holds h8103 h8106
    Inputs1719.k_SU44_TwoNat_holds h641 h642 h643 Inputs1719.k_O4m4_ThreeNat_holds
    Inputs1719.k_O6m4_ThreeNatM_holds
    (gap_18_9_WC_holds h61 h111 h1742 hKU4 Inputs1719.k_L2SzAutRank_holds
      Inputs1719.k_O6m4_ThreeNatM_holds hKfix h)

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

end
