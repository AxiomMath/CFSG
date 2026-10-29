module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTwentyNine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFactsNineteenR
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Chev2StarDef
public import CFSG.GroupTheory.TIQuotientOdd
public import CFSG.GroupTheory.CenterSubgroupOf
public import CFSG.CGT.Foote82.D1Steps
public import CFSG.Timmesfeld.Bridge.Asc72YCount
public import CFSG.GH74.GLS.AssemblyComponents
public import CFSG.GH74.Uniqueness.Section7Lemma711
public import CFSG.GroupTheory.ABGLocalTools.PStabilitySignalizer
public import CFSG.ClassicalInvolution.Q3.Q3OFSplit
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Glue7ChevStar
public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel
public import CFSG.GroupTheory.CardMapInfKer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
open CFSG.LocalAnalysis.UniquenessCase.UC22.F10 (LieAutVocab10)
open scoped Pointwise commutatorElement IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem nineteen_glue_seven (V : LieAutVocab10) (D : Data G) {V₀ Vsub : Subgroup G} {p : ℕ}
    {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ} {A₀ H E K S : Subgroup G}
    (h : Ctx19_23 D V₀ Vsub p L A t B r A₀ H)
    (h12 : R19_12At D V₀ Vsub p L A t B r h.ctx22.ctx)
    (h26 : R19_26At D V₀ Vsub p L A t B r A₀ H h)
    (h27 : R19_27At D V₀ Vsub p L A t B r A₀ H h)
    (h28 : R19_28At D V₀ Vsub p L A t B r A₀ H h)
    (hAV : A ≤ centralizer (V₀ : Set G))
    (h49 : W10_4_9) (hsmall : K_19_glue7_L2small)
    (hJR : K_19_JRgen) (hCh2 : Chev2StarGen)
    (hE : E ≤ A) (hEel : IsElemAbelian r E) (hEcard : Nat.card E = r ^ 2)
    (hK : K ≤ H) (hKcomp : CFSG.IsComponent (K.subgroupOf H))
    (hfaith : ActsFaithfullyOn V₀ K) (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (H ⊓ D.M))
    (h29 : P19_29 V K E A₀ S) :
    R19_glue_7At V D V₀ Vsub p L A t B r A₀ H E K S h hE hEel hEcard hK hKcomp hfaith hS h29 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV0ne : V₀ ≠ ⊥ := ne_bot_of_one_lt_mSub h.ctx22.ctx.hyp.big
  have hV0in : InCalV D.M V₀ := (inCalV0_of_hyp125 h.ctx22.ctx.hyp.hyp125 hV0ne).1
  have hV0el : IsElemAbelian 2 V₀ := hV0in.2.2.2
  have hV0p : IsPGroup 2 V₀ := hV0el.isPGroup
  have hTI : CFSG.CGT.Timmesfeld75.IsTI V₀ := isTI_of_hyp19 h.ctx22.ctx.hyp
  have hV0H : V₀ ≤ H := h.hH ▸ h.ctx22.hV₀
  have hV0M : V₀ ≤ D.M := hV0in.2.1
  have hV0card : 4 ≤ Nat.card V₀ := by
    have hcard : Nat.card V₀ = 2 ^ mSub V₀ := card_eq_two_pow_mSub hV0p
    have hm2 : 2 ≤ mSub V₀ := by have := h.ctx22.ctx.hyp.big; omega
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ mSub V₀ := Nat.pow_le_pow_right (by norm_num) hm2
      _ = Nat.card V₀ := hcard.symm
  have hV0HM : V₀ ≤ H ⊓ D.M := le_inf hV0H hV0M
  have hHMnorm : H ⊓ D.M ≤ normalizer (V₀ : Set G) := by
    rw [normalizer_eq_of_inCalV D hV0in]
    exact inf_le_right
  have hV0S : V₀ ≤ S :=
    CFSG.GH74.Uniqueness.le_of_isSylowOf_of_isPGroup_normal hS hV0HM hHMnorm hV0p
  have hAcomm : IsMulCommutative ↥A := isMulCommutative_of_isZModSq h.ctx22.ctx.hAcard
  have hAH : A ≤ H := A_le_H_of_ctx19_23 h
  have hAM : A ≤ D.M := A_le_M_of_ctx19_10 D h.ctx22.ctx
  have hEH : E ≤ H := hE.trans hAH
  have hEM : E ≤ D.M := hE.trans hAM
  have hE0 : A₀ ≤ E := by
    have : IsMulCommutative ↥A := hAcomm
    have hEeq : E = ((powMonoidHom r : ↥A →* ↥A).ker).map A.subtype :=
      eq_powTorsionSubgroup_of_isElemAbelian_card h.ctx22.ctx.hAcard h.ctx22.ctx.hr.1
        h.ctx22.ctx.hr.2 hE hEel hEcard
    intro x hx
    rw [hEeq]
    refine Subgroup.mem_map.mpr ⟨⟨x, h.ctx22.hA₀ hx⟩, ?_, rfl⟩
    rw [MonoidHom.mem_ker, powMonoidHom_apply]
    have hxr : x ^ Nat.card A₀ = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard A₀ hx)
    have hxr' : x ^ r = 1 := by rwa [h.ctx22.hcard] at hxr
    exact Subtype.ext (by simpa using hxr')
  have hE_NK : E ≤ normalizer (K : Set G) := hE.trans (h27 K hK hKcomp)
  have hA0_le_CK : A₀ ≤ centralizer (K : Set G) :=
    Subgroup.le_centralizer_iff.mpr (h.hH ▸ hK)
  have hKq : CFSG.IsQuasisimple ↥K :=
    (CFSG.IsQuasisimple.congr (Subgroup.subgroupOfEquivOfLe hK)).mp hKcomp.1
  have hKsubH : CFSG.Assembly.IsSubnormal K H :=
    (CFSG.Assembly.IsSubnormal.iff_subgroupOf hK).mpr hKcomp.2
  have hKsubHopen : CFSG.Open.IsSubnormal K H :=
    CFSG.Assembly.isSubnormal_iff_open.mp hKsubH
  have hZsubK : (Zsub K).subgroupOf K = Subgroup.center ↥K := by
    rw [Zsub]
    exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  have hZrelK : CFSG.Open.IsSubnormal (Zsub K) K := by
    refine CFSG.Open.IsSubnormal.step (H := Zsub K) (M := K) (Zsub_le K) ?_
      (CFSG.Open.IsSubnormal.refl K)
    rw [hZsubK]
    infer_instance
  have hZrelH : CFSG.Open.IsSubnormal (Zsub K) H := hZrelK.trans hKsubHopen
  have hZsubH : ((Zsub K).subgroupOf H).IsSubnormal :=
    CFSG.Open.IsSubnormal.subgroupOf hZrelH
  have hPcore_le : pCoreOf 2 K ≤ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K
  have hPcore_norm : K ≤ normalizer (pCoreOf 2 K : Set G) := by
    have hsub : (pCoreOf 2 K).subgroupOf K = CFSG.pCore 2 ↥K := by
      rw [pCoreOf]
      exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hPcore_le).mp (by rw [hsub]; infer_instance)
  have hPcore_normal : ((pCoreOf 2 K).subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPcore_le).mpr hPcore_norm
  have hPcore_subK : CFSG.Open.IsSubnormal (pCoreOf 2 K) K :=
    CFSG.Open.IsSubnormal.step (H := pCoreOf 2 K) (M := K) hPcore_le hPcore_normal
      (CFSG.Open.IsSubnormal.refl K)
  have hPcore_subH : CFSG.Open.IsSubnormal (pCoreOf 2 K) H :=
    hPcore_subK.trans hKsubHopen
  have hPcoreH : pCoreOf 2 (pCoreOf 2 K) ≤ pCoreOf 2 H :=
    CFSG.CGT.Foote82.pCoreOf_le_pCoreOf_of_isSubnormal hPcore_subH
  rw [h.hO2] at hPcoreH
  have hPself : pCoreOf 2 (pCoreOf 2 K) = pCoreOf 2 K := by
    refine le_antisymm (CFSG.LieType.BorelTits.pCoreOf_le 2 _) ?_
    exact CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 _ _ le_rfl
      (by rw [Subgroup.subgroupOf_self]; infer_instance)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
  have hPbot : pCoreOf 2 K = ⊥ := by rw [← hPself]; exact le_bot_iff.mp hPcoreH
  have hKcore : CFSG.pCore 2 ↥K = ⊥ := by
    apply (Subgroup.map_eq_bot_iff_of_injective (H := CFSG.pCore 2 ↥K)
      (f := K.subtype) K.subtype_injective).mp
    simpa [CFSG.Open.pCoreOf] using hPbot
  have hZcenterOdd : Odd (Nat.card (Subgroup.center ↥K)) :=
    CFSG.Timmesfeld.Bridge.Asc72.CentralQuot.odd_card_center hKcore
  have hZodd : Odd (Nat.card (Zsub K)) := by
    rw [Zsub, Subgroup.card_map_of_injective K.subtype_injective]
    exact hZcenterOdd
  have hZleO : Zsub K ≤ Oodd H := by
    have hZH : Zsub K ≤ H := (Zsub_le K).trans hK
    have hcardZ' : Nat.card ↥((Zsub K).subgroupOf H) = Nat.card (Zsub K) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZH).toEquiv
    have hcop : Nat.Coprime 2 (Nat.card ↥((Zsub K).subgroupOf H)) :=
      Nat.coprime_two_left.mpr (by rw [hcardZ']; exact hZodd)
    have hle := CFSG.GH74.GLS.le_pPrimeCore_of_subnormal (X := ↥H) 2 hZsubH hcop
    change (Zsub K).subgroupOf H ≤ CFSG.pPrimeCore 2 ↥H at hle
    have hmap := Subgroup.map_mono (f := H.subtype) hle
    rwa [Subgroup.map_subgroupOf_eq_of_le hZH] at hmap
  have hZleC : Zsub K ≤ centralizer (V₀ : Set G) := by
    have h24_1 : ⁅V₀, Oodd H⁆ = ⊥ := nineteen_twentyfour_one D h
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hmem : ⁅v, z⁆ ∈ ⁅V₀, Oodd H⁆ :=
      Subgroup.commutator_mem_commutator hv (hZleO hz)
    rw [h24_1] at hmem
    exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hmem)
  have hKnotM : ¬ K ≤ D.M := not_le_M_of_actsFaithfullyOn D h hK hKcomp hfaith
  have hSleM : S ≤ D.M := by
    obtain ⟨Q, hQ⟩ := hS
    rw [← hQ]
    rintro s ⟨q, hq, rfl⟩
    exact q.2.2
  have hZKleM : Zsub K ≤ D.M :=
    hZleO.trans (by
      have hOleC : Oodd H ≤ Subgroup.centralizer (V₀ : Set G) := by
        intro o ho
        rw [Subgroup.mem_centralizer_iff]
        intro v hv
        have hmem : ⁅v, o⁆ ∈ ⁅V₀, Oodd H⁆ :=
          Subgroup.commutator_mem_commutator hv ho
        rw [nineteen_twentyfour_one D h] at hmem
        exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hmem)
      exact hOleC.trans (centralizer_le_of_inCalV D hV0in))
  have hV0_NK : V₀ ≤ normalizer (K : Set G) := nineteen_twentyfour_two D h K hK hKcomp
  let P : Subgroup G := S ⊓ normalizer (K : Set G)
  have hV0P : V₀ ≤ P := le_inf hV0S hV0_NK
  let N : Subgroup G := (K ⊔ E ⊔ P) ⊓ normalizer (K : Set G)
  have hPN : P ≤ N := le_inf le_sup_right inf_le_right
  have hV0N : V₀ ≤ N := hV0P.trans hPN
  have hKN : K ≤ N := le_inf (le_sup_left.trans le_sup_left) Subgroup.le_normalizer
  have hEN : E ≤ N := le_inf ((le_sup_right : E ≤ K ⊔ E).trans le_sup_left) hE_NK
  have hNnorm : N ≤ normalizer (K : Set G) := inf_le_right
  have hN_eq : N = K ⊔ E ⊔ P := by
    rw [show N = (K ⊔ E ⊔ P) ⊓ normalizer (K : Set G) from rfl]
    exact inf_eq_left.mpr (sup_le (sup_le Subgroup.le_normalizer hE_NK) inf_le_right)
  let CK : Subgroup ↥N := CFSG.GroupTheory.quasisimpleActionKernel N K inf_le_right
  have : CK.Normal := CFSG.GroupTheory.quasisimpleActionKernel_normal N K inf_le_right
  let G₀ : Type := ↥N ⧸ CK
  let Kbar : Subgroup G₀ := (K.subgroupOf N).map (QuotientGroup.mk' CK)
  let Ebar : Subgroup G₀ := (E.subgroupOf N).map (QuotientGroup.mk' CK)
  let Tbar : Subgroup G₀ := (S.subgroupOf N).map (QuotientGroup.mk' CK)
  let Vbar : Subgroup G₀ := (V₀.subgroupOf N).map (QuotientGroup.mk' CK)
  have hKbar_simple : IsSimpleGroup ↥Kbar := by
    simpa [Kbar, CK, G₀] using
      CFSG.GroupTheory.quasisimple_isSimpleGroup_image N K hKN inf_le_right hKq
  have hKbar_cent : Subgroup.centralizer (Kbar : Set G₀) = ⊥ := by
    simpa [Kbar, CK, G₀] using
      CFSG.GroupTheory.quasisimple_centralizer_image_eq_bot N K hKN inf_le_right hKq
  have hSN_eq : S.subgroupOf N = P.subgroupOf N := by
    ext x
    change ((x : G) ∈ S) ↔ ((x : G) ∈ P)
    exact ⟨fun hxS => ⟨hxS, hNnorm x.2⟩, fun hxP => hxP.1⟩
  have hTbar_syl : CFSG.ABGLocalTools.IsSylowOf 2 Tbar ⊤ := by
    have hPsyl : CFSG.ABGLocalTools.IsSylowOf 2 P N :=
      p_sylow_of_ctx D h h27 h28 hE hEel hEcard hK hKcomp hS
    have hPsub_syl : CFSG.ABGLocalTools.IsSylowOf 2 (P.subgroupOf N) ⊤ := by
      rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff N]
      have htopN : (⊤ : Subgroup ↥N).map N.subtype = N := by
        rw [Subgroup.map_top, Subgroup.range_subtype]
      rw [htopN, Subgroup.map_subgroupOf_eq_of_le hPN]
      exact hPsyl
    have h := uc22p22r_isSylowOf_map_top (QuotientGroup.mk'_surjective CK) hPsub_syl
    simpa [Tbar, hSN_eq] using h
  have hCK : CK = (centralizer (K : Set G)).subgroupOf N :=
    CFSG.GroupTheory.quasisimpleActionKernel_eq_centralizer N K inf_le_right
  have hKbar_normal : Kbar.Normal := by
    have hKnormal : (K.subgroupOf N).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKN).mpr inf_le_right
    exact Subgroup.Normal.map hKnormal (QuotientGroup.mk' CK) (QuotientGroup.mk'_surjective CK)
  have hr7 : 7 ≤ r := by
    have hrodd : Odd r := Odd.of_dvd_nat (odd_card_of_ctx19_10 h.ctx22.ctx) h.ctx22.ctx.hr.2
    have hr2 : r ≠ 2 := by
      intro h2
      rw [h2] at hrodd
      norm_num at hrodd
    have hr3 : r ≠ 3 := r_ne_three h.ctx22.ctx.hAcard h.ctx22.ctx.hr h26
    have h5 : 5 ≤ r := h.ctx22.ctx.hr.1.five_le_of_ne_two_of_ne_three hr2 hr3
    have h6 : r ≠ 6 := by
      intro h6
      rw [h6] at hrodd
      exact absurd hrodd (by decide)
    have hr5 := h.ctx22.ctx.hr5
    omega
  have hrdvd : r ∣ 2 ^ (S17.nOf L) - 1 := by
    obtain ⟨hrp, hrdvdA⟩ := h.ctx22.ctx.hr
    rw [card_eq_of_isZModSq h.ctx22.ctx.hAcard, ← pow_two] at hrdvdA
    exact hrp.dvd_of_dvd_pow hrdvdA
  have hr13 : r ≠ 13 := by
    intro h13
    rw [h13] at hrdvd
    exact not_thirteen_dvd_two_pow_sub_one_of_odd h26 hrdvd
  by_cases hEcent : E ≤ centralizer (K : Set G)
  · have hK_cent : K ≤ centralizer (E : Set G) := Subgroup.le_centralizer_iff.mpr hEcent
    have hE_memU : E ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet D.M := h12 E hE hEel hEcard
    have hNE : normalizer (E : Set G) ≤ D.M :=
      CFSG.LocalAnalysis.RankThreeUC.normalizer_le_of_mem_uniqueSet D.maxLocal hE_memU
    exact (hKnotM (hK_cent.trans ((Subgroup.centralizer_le_normalizer _).trans hNE))).elim
  · have hEcap : E ⊓ centralizer (K : Set G) = A₀ := by
      have hA0le : A₀ ≤ E ⊓ centralizer (K : Set G) := le_inf hE0 hA0_le_CK
      have hdvd : Nat.card ↥(E ⊓ centralizer (K : Set G)) ∣ r ^ 2 := by
        rw [← hEcard]
        exact Subgroup.card_dvd_of_le inf_le_left
      obtain ⟨k, hk_le, hk⟩ := (Nat.dvd_prime_pow h.ctx22.ctx.hr.1).mp hdvd
      have hk_cases : k = 1 ∨ k = 2 := by
        interval_cases k
        · rw [pow_zero] at hk
          have hle : r ≤ 1 := by
            rw [← h.ctx22.hcard]
            exact (Subgroup.card_le_of_le hA0le).trans (le_of_eq hk)
          have hr2 : 2 ≤ r := h.ctx22.ctx.hr.1.two_le
          omega
        · exact Or.inl rfl
        · exact Or.inr rfl
      rcases hk_cases with rfl | rfl
      · have hcardint : Nat.card ↥(E ⊓ centralizer (K : Set G)) = r := by
          simpa using hk
        exact (Subgroup.eq_of_le_of_card_ge hA0le (by rw [hcardint, h.ctx22.hcard])).symm
      · exfalso
        have hcardint : Nat.card ↥(E ⊓ centralizer (K : Set G)) = Nat.card E := by
          rw [hk, hEcard]
        have heq : E ⊓ centralizer (K : Set G) = E :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcardint])
        exact hEcent (heq ▸ inf_le_right)
    have hEin : (E.subgroupOf N) ⊓ CK =
        (E ⊓ centralizer (K : Set G)).subgroupOf N := by
      rw [hCK]
      ext x
      simp [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    have hEbar_card : Nat.card ↥Ebar = r := by
      have hmap := CFSG.GorensteinWalter.card_map_eq_card_mul_card_ker
        (QuotientGroup.mk' CK) (E.subgroupOf N)
      rw [show (QuotientGroup.mk' CK).ker = CK from QuotientGroup.ker_mk' CK,
        hEin, hEcap] at hmap
      have hcardE : Nat.card ↥(E.subgroupOf N) = r ^ 2 := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEN).toEquiv, hEcard]
      have hcardA : Nat.card ↥(A₀.subgroupOf N) = r := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hE0.trans hEN)).toEquiv,
          h.ctx22.hcard]
      rw [hcardE, hcardA] at hmap
      have hmap' : Nat.card ↥Ebar * r = r * r := by
        rw [← hmap, pow_two]
      exact Nat.eq_of_mul_eq_mul_right h.ctx22.ctx.hr.1.pos hmap'
    have hEbar_perm : Permutes Ebar Tbar := by
      have hEP : Permutes E P :=
        CFSG.GroupTheory.permutes_inf_of_le hE_NK (permutes_ES_of_ctx D h h28 hS hE hEel hEcard)
      have hEPN : Permutes (E.subgroupOf N) (P.subgroupOf N) :=
        CFSG.Quasithin.H.Tri.subgroupOf_mul_comm hEN hPN hEP
      change Permutes ((E.subgroupOf N).map (QuotientGroup.mk' CK))
        ((S.subgroupOf N).map (QuotientGroup.mk' CK))
      rw [hSN_eq]
      exact CFSG.GroupTheory.map_permutes_map (QuotientGroup.mk' CK) hEPN
    have hKleM_of : IsChev ↥Kbar 2 → K ≤ D.M := fun hchev2 =>
      le_M_of_isChev_quotient hCh2 D hKN hEN hNnorm hEel.1 (h12 E hE hEel hEcard) hZKleM
        (inf_component_isSylow D h h28 hS hK hKcomp) hSleM CK hCK hKbar_simple hKbar_cent
        hchev2 hTbar_syl h.ctx22.ctx.hr.1 hr7 hr13 hrdvd h26 hEbar_card hEbar_perm
    change (∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ IsChev Kbar q) ∨
      CFSG.LocalAnalysis.UniquenessCase.UC22.F10.IsJankoReeType10 Kbar ∨
      (IsChev Kbar 2 ∧ ∃ x ∈ Ebar, V.InducesField Kbar x) ∨
      (IsChev Kbar 2 ∧ (∀ x ∈ Ebar, ¬ V.InducesField Kbar x) ∧
        ∃ C : Subgroup G₀,
          CFSG.LocalAnalysis.UniquenessCase.UC22.F10.CartanActing10 (Kbar ⊔ Ebar) Tbar C ∧
            Ebar ≤ C) at h29
    rcases h29 with hodd | hJRtype | hfield | hcartan
    · obtain ⟨q, hq, hq2, hchev⟩ := hodd
      let KV : Subgroup G := K ⊔ V₀
      have hKVK : K ≤ KV := le_sup_left
      have hV0KV : V₀ ≤ KV := le_sup_right
      have hKVnorm : KV ≤ normalizer (K : Set G) := sup_le Subgroup.le_normalizer hV0_NK
      have hZKV : Zsub K ≤ KV := (Zsub_le K).trans hKVK
      have : (Subgroup.center ↥K).Characteristic := Subgroup.centerCharacteristic
      have hNK_le_NZ : normalizer (K : Set G) ≤ normalizer (Zsub K : Set G) := by
        intro d hd
        exact CFSG.ABGLocalTools.mem_normalizer_map_subtype_of_characteristic (M := K) hd
      let ZK : Subgroup ↥KV := (Zsub K).subgroupOf KV
      have hZKnormal : ZK.Normal := by
        rw [Subgroup.normal_subgroupOf_iff_le_normalizer hZKV]
        exact hKVnorm.trans hNK_le_NZ
      have : ZK.Normal := hZKnormal
      let Y : Type := ↥KV ⧸ ZK
      let KbY : Subgroup Y := (K.subgroupOf KV).map (QuotientGroup.mk' ZK)
      let TbY : Subgroup Y := (V₀.subgroupOf KV).map (QuotientGroup.mk' ZK)
      have : Finite Y := Finite.of_surjective (QuotientGroup.mk' ZK)
        (QuotientGroup.mk'_surjective ZK)
      have hZK_le_K' : ZK ≤ K.subgroupOf KV := fun x hx => Zsub_le K hx
      have hKZ_Y : (K.subgroupOf KV) ⊓ ZK = Zsub (K.subgroupOf KV) := by
        rw [Zsub, CFSG.GroupTheory.map_center_subgroupOf_eq_subgroupOf_map_center KV K hKVK]
        exact inf_eq_right.mpr hZK_le_K'
      let eYraw := CFSG.ComponentClassification.NormalCenterQuotientImage.equivalence
        (K.subgroupOf KV) ZK (Subgroup.map_injective (Subgroup.subtype_injective _) (by
          rw [Subgroup.subgroupOf_map_subtype, inf_comm]; exact hKZ_Y))
      have hKZ_G : (K.subgroupOf N) ⊓ CK = Zsub (K.subgroupOf N) := by
        rw [Zsub, CFSG.GroupTheory.map_center_subgroupOf_eq_subgroupOf_map_center N K hKN,
          CFSG.center_map_subtype_eq_inf_centralizer, hCK]
        ext x
        simp [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      let eGraw := CFSG.ComponentClassification.NormalCenterQuotientImage.equivalence
        (K.subgroupOf N) CK (Subgroup.map_injective (Subgroup.subtype_injective _) (by
          rw [Subgroup.subgroupOf_map_subtype, inf_comm]; exact hKZ_G))
      have eGq : (↥(K.subgroupOf N) ⧸ Subgroup.center ↥(K.subgroupOf N)) ≃*
          (↥K ⧸ Subgroup.center ↥K) :=
        QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hKN)
          (CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv _)
      have eYq : (↥(K.subgroupOf KV) ⧸ Subgroup.center ↥(K.subgroupOf KV)) ≃*
          (↥K ⧸ Subgroup.center ↥K) :=
        QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hKVK)
          (CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv _)
      have eKG : (↥K ⧸ Subgroup.center ↥K) ≃* ↥Kbar :=
        eGq.symm.trans (by simpa [Kbar] using eGraw)
      have eKY : (↥K ⧸ Subgroup.center ↥K) ≃* ↥KbY :=
        eYq.symm.trans (by simpa [KbY] using eYraw)
      have hKbY_normal : KbY.Normal := by
        have hKnormal : (K.subgroupOf KV).Normal :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer hKVK).mpr hKVnorm
        exact Subgroup.Normal.map hKnormal (QuotientGroup.mk' ZK) (QuotientGroup.mk'_surjective ZK)
      have : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hKq.2.1
      have hKbY_simple : IsSimpleGroup ↥KbY := MulEquiv.isSimpleGroup eKY.symm
      have hKbY_chev : IsChev ↥KbY q := by
        obtain ⟨t, n, f, hadm, hmod⟩ := hchev
        exact ⟨t, n, f, hadm,
          CFSG.Blueprint.LieModel.of_mulEquiv ((eKY.symm.trans eKG).symm) hmod⟩
      have hVsub_comm : IsMulCommutative ↥(V₀.subgroupOf KV) := by
        refine ⟨⟨fun x y => ?_⟩⟩
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z : ↥V₀ => (z : G))
          (isMulCommutative_iff.mp hV0el.1 ⟨x.1.1, x.2⟩ ⟨y.1.1, y.2⟩)
      have : IsMulCommutative ↥(V₀.subgroupOf KV) := hVsub_comm
      have hTbY_el : IsElemAbelian 2 TbY := by
        constructor
        · simpa [TbY] using Subgroup.map_isMulCommutative (V₀.subgroupOf KV) (QuotientGroup.mk' ZK)
        · intro x hx
          obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
          rw [← map_pow]
          have ha2 : a * a = 1 := by
            apply Subtype.ext
            simpa [pow_two] using hV0el.2 (a : G) ha
          rw [show a ^ 2 = 1 by rw [pow_two]; exact ha2, map_one]
      have hV0Zdisj : V₀ ⊓ Zsub K = ⊥ := by
        refine Subgroup.inf_eq_bot_of_coprime ?_
        obtain ⟨m, hm⟩ := hV0p.exists_card_eq
        rw [hm]
        exact (Nat.coprime_two_left.mpr hZodd).pow_left m
      have hJdisj : (V₀.subgroupOf KV) ⊓ ZK = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have hxV : (x : G) ∈ V₀ := hx.1
        have hxZ : (x : G) ∈ Zsub K := hx.2
        have hxbot : (x : G) ∈ (⊥ : Subgroup G) := by
          rw [← hV0Zdisj]
          exact ⟨hxV, hxZ⟩
        exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hxbot))
      have hcardTbY : Nat.card ↥TbY = Nat.card ↥(V₀.subgroupOf KV) := by
        change Nat.card ↥((V₀.subgroupOf KV).map (QuotientGroup.mk' ZK)) =
          Nat.card ↥(V₀.subgroupOf KV)
        exact CFSG.card_map_eq_card_of_inf_ker_eq_bot
          (QuotientGroup.mk' ZK) (by rw [QuotientGroup.ker_mk']; exact hJdisj)
      have hcardVsub : Nat.card ↥(V₀.subgroupOf KV) = Nat.card V₀ :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV0KV).toEquiv
      have hTbY_card : 4 ≤ Nat.card TbY := by
        rw [hcardTbY, hcardVsub]
        exact hV0card
      have hZoddZK : Odd (Nat.card ↥ZK) := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZKV).toEquiv]
        exact hZodd
      have hTbY_centZK : (V₀.subgroupOf KV) ≤ centralizer (ZK : Set ↥KV) := by
        intro v hv
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        apply Subtype.ext
        exact (Subgroup.mem_centralizer_iff.mp (hZleC hz) (v : G) hv).symm
      have hTbY_TI : CFSG.CGT.Timmesfeld75.IsTI TbY := by
        simpa [TbY] using CFSG.GroupTheory.isTI_map_mk'_of_odd
          (hV0p.comap_subtype (K := KV)) (hTI.subgroupOf KV) hZoddZK hTbY_centZK
      have hKbY_top : KbY ⊔ TbY = ⊤ := by
        have hsup : K.subgroupOf KV ⊔ V₀.subgroupOf KV = ⊤ := by
          rw [← Subgroup.subgroupOf_sup hKVK hV0KV]
          exact Subgroup.subgroupOf_self KV
        calc KbY ⊔ TbY = (K.subgroupOf KV ⊔ V₀.subgroupOf KV).map (QuotientGroup.mk' ZK) := by
              rw [Subgroup.map_sup]
          _ = (⊤ : Subgroup ↥KV).map (QuotientGroup.mk' ZK) := by rw [hsup]
          _ = ⊤ := by
              rw [Subgroup.map_top]
              exact MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective ZK)
      have hTbY_faithful : TbY ⊓ Subgroup.centralizer (KbY : Set Y) = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx.1
        have hxcent : (QuotientGroup.mk' ZK) a ∈ Subgroup.centralizer (KbY : Set Y) := hx.2
        have : Group.IsPerfect ↥K := hKq.1
        have hcommZ : ∀ k ∈ K, ⁅k, (a : G)⁆ ∈ Zsub K := by
          intro k hk
          let kKV : ↥KV := ⟨k, hKVK hk⟩
          have hkY : (QuotientGroup.mk' ZK) kKV ∈ KbY :=
            Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hk)
          have hc := Subgroup.mem_centralizer_iff.mp hxcent _ hkY
          have hcomm : (QuotientGroup.mk' ZK) (⁅kKV, a⁆) = 1 := by
            rw [map_commutatorElement]
            exact commutatorElement_eq_one_iff_mul_comm.mpr hc
          have hmemZK : ⁅kKV, a⁆ ∈ ZK := (QuotientGroup.eq_one_iff _).mp hcomm
          have hmemZsub : ((⁅kKV, a⁆ : ↥KV) : G) ∈ Zsub K :=
            Subgroup.mem_subgroupOf.mp (by simpa [ZK] using hmemZK)
          have hcoe : ((⁅kKV, a⁆ : ↥KV) : G) = ⁅k, (a : G)⁆ :=
            map_commutatorElement (f := KV.subtype) kKV a
          rw [hcoe] at hmemZsub
          exact hmemZsub
        have hmemC : (a : G) ∈ Subgroup.centralizer (K : Set G) :=
          mem_centralizer_of_comm_mem_Zsub (hV0_NK ha) hcommZ
        have hzC : (a : G) ∈ V₀ ⊓ Subgroup.centralizer (K : Set G) := ⟨ha, hmemC⟩
        rw [hfaith] at hzC
        have ha1 : (a : G) = 1 := Subgroup.mem_bot.mp hzC
        have ha1' : a = 1 := Subtype.ext ha1
        refine Subgroup.mem_bot.mpr ?_
        change (QuotientGroup.mk' ZK) a = 1
        rw [ha1', map_one]
      have hcardKbY : Nat.card ↥KbY = 60 ∨ Nat.card ↥KbY = 168 ∨ Nat.card ↥KbY = 360 :=
        h49 Y KbY TbY hKbY_normal hKbY_simple ⟨q, hq, hq2, hKbY_chev⟩
          hTbY_el hTbY_card hTbY_faithful hKbY_top hTbY_TI
      have hcard_eq : Nat.card ↥KbY = Nat.card ↥Kbar :=
        Nat.card_congr (eKY.symm.trans eKG).toEquiv
      have hKbar_card : Nat.card ↥Kbar = 60 ∨ Nat.card ↥Kbar = 168 ∨
          Nat.card ↥Kbar = 360 := by
        rcases hcardKbY with h | h | h
        · exact Or.inl (by rw [← hcard_eq]; exact h)
        · exact Or.inr (Or.inl (by rw [← hcard_eq]; exact h))
        · exact Or.inr (Or.inr (by rw [← hcard_eq]; exact h))
      have hEbar_nontriv : Nontrivial ↥Ebar :=
        Finite.one_lt_card_iff_nontrivial.mp
          (by rw [hEbar_card]; exact h.ctx22.ctx.hr.1.one_lt)
      obtain ⟨e, he1⟩ := exists_ne (1 : ↥Ebar)
      have he_order : orderOf (e : G₀) = r := by
        have hdvd : orderOf (e : G₀) ∣ r := by
          rw [← hEbar_card]
          exact Subgroup.orderOf_dvd_natCard Ebar e.2
        rcases (Nat.dvd_prime h.ctx22.ctx.hr.1).mp hdvd with h1 | hr
        · exfalso
          apply he1
          apply Subtype.ext
          exact orderOf_eq_one_iff.mp h1
        · exact hr
      have hV0nontriv : Nontrivial ↥V₀ :=
        Finite.one_lt_card_iff_nontrivial.mp (by omega : 1 < Nat.card V₀)
      obtain ⟨v₀, hv0ne⟩ := exists_ne (1 : ↥V₀)
      have hv0sq : v₀ ^ 2 = 1 := by
        apply Subtype.ext
        simpa [pow_two] using hV0el.2 (v₀ : G) v₀.2
      have hv0ord : orderOf (v₀ : G) = 2 := by
        have hdvd : orderOf (v₀ : G) ∣ 2 :=
          orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hv0sq)
        rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
        · exfalso
          exact hv0ne (Subtype.ext (orderOf_eq_one_iff.mp h1))
        · exact h2
      let v : G₀ := (QuotientGroup.mk' CK) ⟨v₀, hV0N v₀.2⟩
      have hv_mem : v ∈ Vbar :=
        Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr v₀.2)
      have hv_ne : v ≠ 1 := by
        intro hv
        have hmem : (⟨v₀, hV0N v₀.2⟩ : ↥N) ∈ CK := (QuotientGroup.eq_one_iff _).mp hv
        have hmem' : (⟨v₀, hV0N v₀.2⟩ : ↥N) ∈
            (Subgroup.centralizer (K : Set G)).subgroupOf N := by
          simpa [hCK] using hmem
        have hvC : (v₀ : G) ∈ Subgroup.centralizer (K : Set G) := hmem'
        have hbot : (v₀ : G) ∈ (⊥ : Subgroup G) := by
          rw [← hfaith]
          exact ⟨v₀.2, hvC⟩
        exact hv0ne (Subtype.ext (Subgroup.mem_bot.mp hbot))
      have hv_order : orderOf v = 2 := by
        have hxord : orderOf (⟨v₀, hV0N v₀.2⟩ : ↥N) = 2 :=
          (Subgroup.orderOf_coe _).symm.trans hv0ord
        have hdvd : orderOf v ∣ 2 := by
          have h := orderOf_map_dvd (QuotientGroup.mk' CK) (⟨v₀, hV0N v₀.2⟩ : ↥N)
          rwa [hxord] at h
        rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
        · exact absurd (orderOf_eq_one_iff.mp h1) hv_ne
        · exact h2
      have hcomm_ev : (e : G₀) * v = v * (e : G₀) := by
        obtain ⟨eE, heE, heeq⟩ := Subgroup.mem_map.mp e.2
        rw [← heeq]
        have hcommG : (eE : G) * (v₀ : G) = (v₀ : G) * (eE : G) :=
          (Subgroup.mem_centralizer_iff.mp (hAV (hE heE)) (v₀ : G) v₀.2).symm
        have hcommN : eE * ⟨v₀, hV0N v₀.2⟩ = ⟨v₀, hV0N v₀.2⟩ * eE :=
          Subtype.ext hcommG
        exact congrArg (QuotientGroup.mk' CK) hcommN
      exact hsmall G₀ Kbar hKbar_normal hKbar_simple hKbar_cent hKbar_card
        (e : G₀) v (by rw [he_order]; exact h.ctx22.ctx.hr.1)
        (by rw [he_order]; exact hr7) hv_order hcomm_ev
    ·
      have hKZ_G : (K.subgroupOf N) ⊓ CK = Zsub (K.subgroupOf N) := by
        rw [Zsub, CFSG.GroupTheory.map_center_subgroupOf_eq_subgroupOf_map_center N K hKN,
          CFSG.center_map_subtype_eq_inf_centralizer, hCK]
        ext x
        simp [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      have hKbar_nonab : ∃ a b : ↥Kbar, a * b ≠ b * a := by
        simpa [Kbar, CK, G₀] using
          CFSG.GroupTheory.quasisimple_nonabelian_image N K hKN inf_le_right hKq
      have : IsSimpleGroup G := D.standing.simple
      have hHne_top : H ≠ ⊤ := by
        intro hHtop
        have hcenter : Subgroup.center G = ⊥ :=
          CFSG.Walter.center_eq_bot_of_isSimpleGroup D.standing.nonab
        have hA0center : A₀ ≤ Subgroup.center G := by
          intro a ha
          rw [Subgroup.mem_center_iff]
          intro g
          have hg : g ∈ Subgroup.centralizer (A₀ : Set G) := by
            rw [← h.hH, hHtop]
            exact Subgroup.mem_top g
          exact (Subgroup.mem_centralizer_iff.mp hg a ha).symm
        have hA0bot : A₀ = ⊥ := le_bot_iff.mp (hA0center.trans (le_of_eq hcenter))
        have hcard := h.ctx22.hcard
        rw [hA0bot, Subgroup.card_bot] at hcard
        have hr2 : 2 ≤ r := h.ctx22.ctx.hr.1.two_le
        omega
      have hKne_top : K ≠ ⊤ := fun hKtop => hHne_top (top_unique (hKtop ▸ hK))
      let φ : ↥K →* ↥Kbar :=
        MonoidHom.codRestrict ((QuotientGroup.mk' CK).comp (Subgroup.inclusion hKN)) Kbar
          (fun k => Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr k.2))
      have hφ_surj : Function.Surjective φ := by
        rintro ⟨y, hy⟩
        obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective CK y
        obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp hy
        have hxK : (x : G) ∈ K := Subgroup.mem_subgroupOf.mp hx
        refine ⟨⟨(x : G), hxK⟩, ?_⟩
        apply Subtype.ext
        exact hxeq
      have hKbar_cat : CFSG.Open.IsCatalogGroup ↥Kbar :=
        CFSG.KCore.KProperNonab.catalogue_of_surjective CFSG.Open.isCatalogGroup_isoInvariant
          D.standing.kProper K hKne_top hKbar_nonab φ hφ_surj
      let imgV : ↥V₀ →* G₀ := (QuotientGroup.mk' CK).comp (Subgroup.inclusion hV0N)
      have himgV_mem : ∀ x : ↥V₀, imgV x ∈ Vbar := fun x =>
        Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr x.2)
      have himgV_inj : Function.Injective imgV := by
        rw [← MonoidHom.ker_eq_bot_iff]
        rw [eq_bot_iff]
        intro x hx
        rw [MonoidHom.mem_ker] at hx
        have hx' : (QuotientGroup.mk' CK) (⟨x, hV0N x.2⟩ : ↥N) = 1 := hx
        have hxC' : Subgroup.inclusion hV0N x ∈
            (Subgroup.centralizer (K : Set G)).subgroupOf N := by
          rw [← hCK]
          exact (QuotientGroup.eq_one_iff (Subgroup.inclusion hV0N x)).mp hx
        have hxC : (x : G) ∈ Subgroup.centralizer (K : Set G) := hxC'
        have hbot : (x : G) ∈ (⊥ : Subgroup G) := by
          rw [← hfaith]
          exact ⟨x.2, hxC⟩
        exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hbot))
      have himgV_order : ∀ x : ↥V₀, x ≠ 1 → orderOf (imgV x) = 2 := by
        intro x hxne
        have hx2 : x ^ 2 = 1 := by
          apply Subtype.ext
          simpa [pow_two] using hV0el.2 (x : G) x.2
        have hxord : orderOf x = 2 := by
          have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
          rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
          · exact absurd (orderOf_eq_one_iff.mp h1) hxne
          · exact h2
        rw [orderOf_injective imgV himgV_inj x, hxord]
      have hV0nontriv : Nontrivial ↥V₀ :=
        Finite.one_lt_card_iff_nontrivial.mp (by omega : 1 < Nat.card V₀)
      obtain ⟨v0, hv0ne⟩ := exists_ne (1 : ↥V₀)
      have hv0sqG : (v0 : G) * (v0 : G) = 1 := by
        simpa [pow_two] using hV0el.2 (v0 : G) v0.2
      have hv0ord : orderOf v0 = 2 := by
        have h2 : v0 ^ 2 = 1 := by
          apply Subtype.ext
          simpa [pow_two] using hV0el.2 (v0 : G) v0.2
        have hdvd : orderOf v0 ∣ 2 := orderOf_dvd_of_pow_eq_one h2
        rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
        · exact absurd (orderOf_eq_one_iff.mp h1) hv0ne
        · exact h2
      have hex : ∃ w0 : ↥V₀, w0 ∉ Subgroup.zpowers v0 := by
        by_contra h
        push Not at h
        have hle : (⊤ : Subgroup ↥V₀) ≤ Subgroup.zpowers v0 := fun x _ => h x
        have hcardle := Subgroup.card_le_of_le hle
        rw [Nat.card_zpowers, hv0ord] at hcardle
        have hcardle' : Nat.card ↥V₀ ≤ 2 := by simpa using hcardle
        have hV0card' : 4 ≤ Nat.card ↥V₀ := by simpa using hV0card
        omega
      obtain ⟨w0, hw0⟩ := hex
      have hw0ne : w0 ≠ 1 := by
        intro h1
        exact hw0 (by rw [h1]; exact Subgroup.one_mem _)
      have hw0sqG : (w0 : G) * (w0 : G) = 1 := by
        simpa [pow_two] using hV0el.2 (w0 : G) w0.2
      have hw0ord : orderOf w0 = 2 := by
        have h2 : w0 ^ 2 = 1 := by
          apply Subtype.ext
          simpa [pow_two] using hV0el.2 (w0 : G) w0.2
        have hdvd : orderOf w0 ∣ 2 := orderOf_dvd_of_pow_eq_one h2
        rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
        · exact absurd (orderOf_eq_one_iff.mp h1) hw0ne
        · exact h2
      have hw0ne_v0 : w0 ≠ v0 := by
        intro h1
        exact hw0 (by rw [h1]; exact Subgroup.mem_zpowers v0)
      have hv0w0 : v0 ≠ w0 := fun h => hw0ne_v0 h.symm
      have hgen := hJR G₀ Kbar hKbar_normal hKbar_simple hKbar_cent hKbar_cat hJRtype
        (imgV v0) (imgV w0) (himgV_order v0 hv0ne) (himgV_order w0 hw0ne)
        (fun h => hv0w0 (himgV_inj h))
        (by
          rw [← map_mul, ← map_mul]
          exact congrArg imgV (isMulCommutative_iff.mp hV0el.1 v0 w0))
      let A : Subgroup G₀ := Kbar ⊓ Subgroup.centralizer ({imgV v0} : Set G₀)
      let B : Subgroup G₀ := Kbar ⊓ Subgroup.centralizer ({imgV w0} : Set G₀)
      have hA : A ≤ (K.subgroupOf N).map (QuotientGroup.mk' CK) := inf_le_left
      have hB : B ≤ (K.subgroupOf N).map (QuotientGroup.mk' CK) := inf_le_left
      have hKsplit : K.subgroupOf N ≤
          (A.comap (QuotientGroup.mk' CK) ⊓ K.subgroupOf N) ⊔
            (B.comap (QuotientGroup.mk' CK) ⊓ K.subgroupOf N) ⊔
              ((QuotientGroup.mk' CK).ker ⊓ K.subgroupOf N) :=
        CFSG.GroupTheory.le_sup_comap_of_map_le (QuotientGroup.mk' CK) hA hB
          (by simpa [Kbar] using hgen)
      have hv0M : Subgroup.centralizer ({(v0 : G)} : Set G) ≤ D.M := by
        rw [← normalizer_eq_of_inCalV D hV0in]
        exact CFSG.LocalAnalysis.WeakClosure81.centralizer_le_normalizer_of_isTI hTI v0.2
          (fun h => hv0ne (Subtype.ext h))
      have hw0M : Subgroup.centralizer ({(w0 : G)} : Set G) ≤ D.M := by
        rw [← normalizer_eq_of_inCalV D hV0in]
        exact CFSG.LocalAnalysis.WeakClosure81.centralizer_le_normalizer_of_isTI hTI w0.2
          (fun h => hw0ne (Subtype.ext h))
      have hZKleM : Zsub K ≤ D.M :=
        hZleO.trans (by
          have hOleC : Oodd H ≤ Subgroup.centralizer (V₀ : Set G) := by
            intro o ho
            rw [Subgroup.mem_centralizer_iff]
            intro v hv
            have hmem : ⁅v, o⁆ ∈ ⁅V₀, Oodd H⁆ :=
              Subgroup.commutator_mem_commutator hv ho
            rw [nineteen_twentyfour_one D h] at hmem
            exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hmem)
          exact hOleC.trans (centralizer_le_of_inCalV D hV0in))
      have hKnormN : (K.subgroupOf N).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hKN).mpr inf_le_right
      have hApre_le_M : ((A.comap (QuotientGroup.mk' CK) ⊓ K.subgroupOf N).map N.subtype) ≤
          D.M := by
        rintro y ⟨x, hx, rfl⟩
        have hxK : (x : G) ∈ K := hx.2
        have hxcent : (QuotientGroup.mk' CK) x ∈
            Subgroup.centralizer ({imgV v0} : Set G₀) := hx.1.2
        have hcommY : (QuotientGroup.mk' CK) x * imgV v0 =
            imgV v0 * (QuotientGroup.mk' CK) x :=
          (Subgroup.mem_centralizer_iff.mp hxcent _ (by simp)).symm
        have hcommN : (QuotientGroup.mk' CK) (⁅x, (⟨v0, hV0N v0.2⟩ : ↥N)⁆) = 1 := by
          rw [map_commutatorElement]
          exact commutatorElement_eq_one_iff_mul_comm.mpr hcommY
        have hmemCK : ⁅x, (⟨v0, hV0N v0.2⟩ : ↥N)⁆ ∈ CK :=
          (QuotientGroup.eq_one_iff _).mp hcommN
        have hmemC' : (⁅x, (⟨v0, hV0N v0.2⟩ : ↥N)⁆ : ↥N) ∈
            (Subgroup.centralizer (K : Set G)).subgroupOf N := by
          simpa [hCK] using hmemCK
        have hmemC : ((⁅x, (⟨v0, hV0N v0.2⟩ : ↥N)⁆ : ↥N) : G) ∈
            Subgroup.centralizer (K : Set G) := hmemC'
        have hcoe : ((⁅x, (⟨v0, hV0N v0.2⟩ : ↥N)⁆ : ↥N) : G) =
            ⁅(x : G), (v0 : G)⁆ :=
          map_commutatorElement (f := N.subtype) x (⟨v0, hV0N v0.2⟩ : ↥N)
        rw [hcoe] at hmemC
        have hmemK' : ⁅x, (⟨v0, hV0N v0.2⟩ : ↥N)⁆ ∈ K.subgroupOf N := by
          have hconj : (⟨v0, hV0N v0.2⟩ : ↥N) * x⁻¹ * (⟨v0, hV0N v0.2⟩ : ↥N)⁻¹ ∈
              K.subgroupOf N :=
            hKnormN.conj_mem x⁻¹ ((K.subgroupOf N).inv_mem hx.2) (⟨v0, hV0N v0.2⟩ : ↥N)
          have hmul : x * ((⟨v0, hV0N v0.2⟩ : ↥N) * x⁻¹ * (⟨v0, hV0N v0.2⟩ : ↥N)⁻¹) ∈
              K.subgroupOf N := (K.subgroupOf N).mul_mem hx.2 hconj
          rw [commutatorElement_def]
          convert hmul using 1 <;> group
        have hmemK : ⁅(x : G), (v0 : G)⁆ ∈ K := Subgroup.mem_subgroupOf.mp hmemK'
        have hmemZ : ⁅(x : G), (v0 : G)⁆ ∈ Zsub K := by
          rw [Zsub, CFSG.center_map_subtype_eq_inf_centralizer]
          exact ⟨hmemK, hmemC⟩
        have hcomm_odd : (v0 : G) * (x : G) * (v0 : G)⁻¹ * (x : G)⁻¹ ∈ Zsub K := by
          have hinv := (Zsub K).inv_mem hmemZ
          convert hinv using 1 <;> group
        have hcentZ : ∀ o ∈ Zsub K, o * (v0 : G) = (v0 : G) * o := by
          intro o ho
          exact (Subgroup.mem_centralizer_iff.mp (hZleC ho) (v0 : G) v0.2).symm
        have hcomm_odd' : (x : G) * (v0 : G) * (x : G)⁻¹ * (v0 : G)⁻¹ ∈ Zsub K := by
          have hinv := (Zsub K).inv_mem hcomm_odd
          convert hinv using 1 <;> group
        have hv0x : (v0 : G) * (x : G) = (x : G) * (v0 : G) :=
          (CFSG.ClassicalInvolution.Q3.Q3OF.commute_of_commutator_mem_odd
            (a := (v0 : G)) (l := (x : G)) hZodd hv0sqG
            (fun o ho => (hcentZ o ho).symm) hcomm_odd').symm
        have hv0x' : (x : G) ∈ Subgroup.centralizer ({(v0 : G)} : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro v hv
          rw [Set.mem_singleton_iff] at hv
          rw [hv]
          exact hv0x
        exact hv0M hv0x'
      have hBpre_le_M : ((B.comap (QuotientGroup.mk' CK) ⊓ K.subgroupOf N).map N.subtype) ≤
          D.M := by
        rintro y ⟨x, hx, rfl⟩
        have hxK : (x : G) ∈ K := hx.2
        have hxcent : (QuotientGroup.mk' CK) x ∈
            Subgroup.centralizer ({imgV w0} : Set G₀) := hx.1.2
        have hcommY : (QuotientGroup.mk' CK) x * imgV w0 =
            imgV w0 * (QuotientGroup.mk' CK) x :=
          (Subgroup.mem_centralizer_iff.mp hxcent _ (by simp)).symm
        have hcommN : (QuotientGroup.mk' CK) (⁅x, (⟨w0, hV0N w0.2⟩ : ↥N)⁆) = 1 := by
          rw [map_commutatorElement]
          exact commutatorElement_eq_one_iff_mul_comm.mpr hcommY
        have hmemCK : ⁅x, (⟨w0, hV0N w0.2⟩ : ↥N)⁆ ∈ CK :=
          (QuotientGroup.eq_one_iff _).mp hcommN
        have hmemC' : (⁅x, (⟨w0, hV0N w0.2⟩ : ↥N)⁆ : ↥N) ∈
            (Subgroup.centralizer (K : Set G)).subgroupOf N := by
          simpa [hCK] using hmemCK
        have hmemC : ((⁅x, (⟨w0, hV0N w0.2⟩ : ↥N)⁆ : ↥N) : G) ∈
            Subgroup.centralizer (K : Set G) := hmemC'
        have hcoe : ((⁅x, (⟨w0, hV0N w0.2⟩ : ↥N)⁆ : ↥N) : G) =
            ⁅(x : G), (w0 : G)⁆ :=
          map_commutatorElement (f := N.subtype) x (⟨w0, hV0N w0.2⟩ : ↥N)
        rw [hcoe] at hmemC
        have hmemK' : ⁅x, (⟨w0, hV0N w0.2⟩ : ↥N)⁆ ∈ K.subgroupOf N := by
          have hconj : (⟨w0, hV0N w0.2⟩ : ↥N) * x⁻¹ * (⟨w0, hV0N w0.2⟩ : ↥N)⁻¹ ∈
              K.subgroupOf N :=
            hKnormN.conj_mem x⁻¹ ((K.subgroupOf N).inv_mem hx.2) (⟨w0, hV0N w0.2⟩ : ↥N)
          have hmul : x * ((⟨w0, hV0N w0.2⟩ : ↥N) * x⁻¹ * (⟨w0, hV0N w0.2⟩ : ↥N)⁻¹) ∈
              K.subgroupOf N := (K.subgroupOf N).mul_mem hx.2 hconj
          rw [commutatorElement_def]
          convert hmul using 1 <;> group
        have hmemK : ⁅(x : G), (w0 : G)⁆ ∈ K := Subgroup.mem_subgroupOf.mp hmemK'
        have hmemZ : ⁅(x : G), (w0 : G)⁆ ∈ Zsub K := by
          rw [Zsub, CFSG.center_map_subtype_eq_inf_centralizer]
          exact ⟨hmemK, hmemC⟩
        have hcomm_odd : (w0 : G) * (x : G) * (w0 : G)⁻¹ * (x : G)⁻¹ ∈ Zsub K := by
          have hinv := (Zsub K).inv_mem hmemZ
          convert hinv using 1 <;> group
        have hcentZ : ∀ o ∈ Zsub K, o * (w0 : G) = (w0 : G) * o := by
          intro o ho
          exact (Subgroup.mem_centralizer_iff.mp (hZleC ho) (w0 : G) w0.2).symm
        have hcomm_odd' : (x : G) * (w0 : G) * (x : G)⁻¹ * (w0 : G)⁻¹ ∈ Zsub K := by
          have hinv := (Zsub K).inv_mem hcomm_odd
          convert hinv using 1 <;> group
        have hw0x : (w0 : G) * (x : G) = (x : G) * (w0 : G) :=
          (CFSG.ClassicalInvolution.Q3.Q3OF.commute_of_commutator_mem_odd
            (a := (w0 : G)) (l := (x : G)) hZodd hw0sqG
            (fun o ho => (hcentZ o ho).symm) hcomm_odd').symm
        have hw0x' : (x : G) ∈ Subgroup.centralizer ({(w0 : G)} : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro v hv
          rw [Set.mem_singleton_iff] at hv
          rw [hv]
          exact hw0x
        exact hw0M hw0x'
      have hKerpre_le_M : (((QuotientGroup.mk' CK).ker ⊓ K.subgroupOf N).map N.subtype) ≤
          D.M := by
        rintro y ⟨x, hx, rfl⟩
        have hxker : x ∈ (QuotientGroup.mk' CK).ker := hx.1
        have hxK : x ∈ K.subgroupOf N := hx.2
        have hxCK : x ∈ CK := by simpa using hxker
        have hxZ' : x ∈ Zsub (K.subgroupOf N) := by
          rw [← hKZ_G]
          exact ⟨hxK, hxCK⟩
        rw [Zsub, CFSG.GroupTheory.map_center_subgroupOf_eq_subgroupOf_map_center N K hKN]
          at hxZ'
        exact hZKleM hxZ'
      have hKleM : K ≤ D.M := by
        have hmap := Subgroup.map_mono (f := N.subtype) hKsplit
        rw [Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hKN] at hmap
        exact hmap.trans (sup_le (sup_le hApre_le_M hBpre_le_M) hKerpre_le_M)
      exact hKnotM hKleM
    · exact hKnotM (hKleM_of hfield.1)
    · exact hKnotM (hKleM_of hcartan.1)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
