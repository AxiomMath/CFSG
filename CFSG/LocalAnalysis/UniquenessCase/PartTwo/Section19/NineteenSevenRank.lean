module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Ctx19One
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenNineFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeS
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1c
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22rj
public import CFSG.LocalAnalysis.UniquenessCase.UC6N588A1
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15SecRank
public import CFSG.GroupTheory.E3Params
public import CFSG.GroupTheory.PRankCommutingPerfect
public import CFSG.ClassicalGroups.PCoreSection
public import CFSG.Quasithin.Background.E3MParamAttained

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12
open CFSG.Quasithin CFSG.LocalAnalysis.WeakClosure81
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem nineteen_seven_not_dvd_index (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K) (h5 : R19_5At D V₀ V p L K h) {v : G}
    (hv : v ∈ V) (hv0 : v ∉ V₀) :
    ¬ 5 ∣ ((D.M ⊓ centralizer ({v} : Set G)).subgroupOf (F11.CElt D.M V₀ v)).index := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨Q, hQ⟩ := h5 v hv hv0
  rw [cElt_eq_centModInM D V₀ v]
  intro h5dvd
  have hQH : (Q : Subgroup ↥(centModInM D V₀ v)) ≤
      (D.M ⊓ centralizer ({v} : Set G)).subgroupOf (centModInM D V₀ v) := by
    intro q hq
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨q.2.1, hQ ⟨q, hq, rfl⟩⟩
  exact (Sylow.not_dvd_index Q) (h5dvd.trans (Subgroup.index_dvd_of_le hQH))

theorem nineteen_seven_pRank_cTilde_le_one (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K) (h5 : R19_5At D V₀ V p L K h)
    (h61 : UC6.R6_1 D) :
    CFSG.Open.pRank 5 (F11.CTilde D.M V₀ V) ≤ 1 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hV0 : InCalV0 D.M V₀ V :=
    inCalV0_of_hyp125 h.hyp.hyp125 (ne_bot_of_one_lt_mSub h.hyp.big)
  by_contra hcon
  have h2 : 2 ≤ CFSG.Open.pRank 5 (F11.CTilde D.M V₀ V) := by omega
  obtain ⟨E, hEC, hEel, hEcard⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank Nat.prime_five (k := 2) h2
  have hEp : IsPGroup 5 E := IsElemAbelian.isPGroup hEel
  have hne : V ≠ V₀ := fun hEq => hV0.2.2.2.2.1 (hEq ▸ hV0.2.2.2.1)
  have hcov : ∀ u ∈ V, u ∉ V₀ → ∃ X : Subgroup G, X ≤ D.M ∧ UniqueMax D.M X ∧
      X ≤ centralizer ({u} : Set G) := by
    intro u hu hu0
    obtain ⟨Q, hQ⟩ := h5 u hu hu0
    have hCTle : F11.CTilde D.M V₀ V ≤ centModInM D V₀ u := by
      rw [← cElt_eq_centModInM D V₀ u]
      unfold F11.CTilde
      exact iInf_le_of_le u (iInf_le_of_le hu le_rfl)
    obtain ⟨P, hP⟩ :=
      (hEp.comap_subtype (K := centModInM D V₀ u)).exists_le_sylow
    obtain ⟨c, hc⟩ := MulAction.exists_smul_eq ↥(centModInM D V₀ u) P Q
    have hQM : Q.map (centModInM D V₀ u).subtype ≤ D.M := by
      rintro _ ⟨q, -, rfl⟩
      exact q.2.1
    have hE'Q : E.map (MulAut.conj (c : G)).toMonoidHom ≤
        Q.map (centModInM D V₀ u).subtype := by
      rintro _ ⟨x, hx, rfl⟩
      have hxC : x ∈ centModInM D V₀ u := hCTle (hEC hx)
      have hxP : (⟨x, hxC⟩ : ↥(centModInM D V₀ u)) ∈
          (P : Subgroup ↥(centModInM D V₀ u)) :=
        hP (Subgroup.mem_subgroupOf.mpr hx)
      have hxQ : (c : ↥(centModInM D V₀ u)) * ⟨x, hxC⟩ *
          (c : ↥(centModInM D V₀ u))⁻¹ ∈ (Q : Subgroup ↥(centModInM D V₀ u)) := by
        rw [← hc, Sylow.coe_subgroup_smul]
        exact Subgroup.smul_mem_pointwise_smul _ (MulAut.conj c) _ hxP
      simpa using Subgroup.mem_map_of_mem (centModInM D V₀ u).subtype hxQ
    have hE'el : IsElemAbelian 5 (E.map (MulAut.conj (c : G)).toMonoidHom) :=
      CFSG.SectionRank.isElemAbelian_map hEel _
    have hE'p : IsPGroup 5 (E.map (MulAut.conj (c : G)).toMonoidHom) :=
      IsElemAbelian.isPGroup hE'el
    have hE'card : Nat.card (E.map (MulAut.conj (c : G)).toMonoidHom) = 5 ^ 2 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj (c : G)).injective, hEcard]
    have hE'c : ¬ IsCyclic (E.map (MulAut.conj (c : G)).toMonoidHom) :=
      RankThreeUC.S15.not_isCyclic_of_isElemAbelian Nat.prime_five (by norm_num) hE'el hE'card
    exact ⟨Q.map (centModInM D V₀ u).subtype, hQM,
      c23_uniqueMax_of_noncyclic D h61 (h.p_eq ▸ h.hyp.hp) hE'p hE'c hE'Q hQM, hQ⟩
  obtain ⟨u, hu, hu0⟩ := Set.not_subset.mp fun hle => hne (le_antisymm hle hV0.2.2.1)
  exact hV0.2.2.2.2.1
    (ElevenNine.isTI_of_cover_uniqueMax D hV0.2.1 hV0.1 (isTI_of_hyp19 h.hyp) hcov)

theorem nineteen_seven_two_le_pRank_mbar (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K) (hV : IsElemAbelian 2 V)
    (h5 : R19_5At D V₀ V p L K h) (hx : DataExt D) (h61 : UC6.R6_1 D) :
    2 ≤ CFSG.Open.pRank 5 (Mbar D.M V₀ V hV) := by
  have hP : PairFacts D.M V₀ V := h.hyp.hyp125.pairFacts
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  haveI : ((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal :=
    s15_Three_cTilde_normal hV hMs
  have h1 : CFSG.Open.pRank 5 D.M - 1 ≤
      CFSG.Open.pRank 5 (⊤ : Subgroup ↥(Mbar D.M V₀ V hV)) := by
    rw [← s15_Three_pRank_MBar11 hV hMs 5]
    exact uc22p22q_pRank_sub_one_le Nat.prime_five (C := F11.CTilde D.M V₀ V)
      (nineteen_seven_pRank_cTilde_le_one D h h5 h61)
  have h3 : 3 ≤ CFSG.Open.pRank 5 D.M := h.p_eq ▸ hx.three_le p h.hyp.hp
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
  omega

theorem nineteen_seven_exists_involution (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K) (hV : IsElemAbelian 2 V)
    (h5 : R19_5At D V₀ V p L K h) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (hm : ¬ MBarGT D.M V₀ V 3) :
    ∃ t : MulAut (Vtil V₀ V hV), t ∈ Mbar D.M V₀ V hV ∧ orderOf t = 2 ∧
      E3.mQuot (⊤ : Subgroup (Vtil V₀ V hV)) (fixV (Subgroup.zpowers t)) ≤ 3 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : PairFacts D.M V₀ V := h.hyp.hyp125.pairFacts
  have hmP : E3.mParam (Mbar D.M V₀ V hV) ≤ 3 := by
    have hnot := (PartTwo.mBarGT_iff_lt_mBar D.M V₀ V hV hP.le hP.le_normalizer
      hP.le_normalizer₀ 3).not.mp hm
    have hle : mBar D.M V₀ V hV ≤ 3 := by omega
    exact hle
  by_cases hev : Even (Nat.card (Mbar D.M V₀ V hV))
  · obtain ⟨t, ht, hord, hval⟩ :=
      E3.exists_involution_rkIdx_fixV_eq_mParam (Mbar D.M V₀ V hV) hev
    refine ⟨t, ht, hord, ?_⟩
    rw [CFSG.GroupTheory.mQuot_top_eq_rkIdx, hval]
    exact hmP
  · exfalso
    unfold E3.mParam at hmP
    rw [if_neg hev] at hmP
    have hsq : ∀ w : Vtil V₀ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
    have hpV : IsPGroup 2 (Vtil V₀ V hV) := CFSG.Quasithin.isPGroup_two_of_sq_eq_one hsq
    have h8 : Nat.card (Vtil V₀ V hV) ≤ 8 := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := Vtil V₀ V hV)).mp hpV
      have hkrk : rk (Vtil V₀ V hV) = k := by
        unfold CFSG.Quasithin.rk
        rw [hk, padicValNat.prime_pow]
      rw [hk, ← hkrk]
      calc 2 ^ rk (Vtil V₀ V hV) ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hmP
        _ = 8 := by norm_num
    have h5dvd : 5 ∣ Nat.card (Mbar D.M V₀ V hV) := by
      have h2 : 2 ≤ CFSG.Open.pRank 5 (Mbar D.M V₀ V hV) :=
        nineteen_seven_two_le_pRank_mbar D h hV h5 hx h61
      obtain ⟨E5, hE5, hE5el, hE5card⟩ :=
        CFSG.SectionRank.exists_pRank (p := 5) (by norm_num) (Mbar D.M V₀ V hV)
      have h1 : 5 ∣ Nat.card E5 := by
        rw [hE5card]
        exact dvd_pow_self 5 (by omega : CFSG.Open.pRank 5 (Mbar D.M V₀ V hV) ≠ 0)
      exact h1.trans (Subgroup.card_dvd_of_le hE5)
    obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Mbar D.M V₀ V hV)) 5 h5dvd
    exact CFSG.GroupTheory.no_orderOf_five_mulAut hpV h8
      (σ := (x : MulAut (Vtil V₀ V hV))) (by simpa using hxord)

theorem nineteen_seven_two_le_pRank_sup (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K) :
    2 ≤ CFSG.Open.pRank 5 (L ⊔ K) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hLKleM : L ⊔ K ≤ D.M := sup_le h.hyp.hL.1.1.le h.hK.1.le
  have hcomm1 : ⁅L, K⁆ ≤ CFSG.Open.pCoreOf 2 D.M :=
    (calC_commutator_le_of_ne h.hyp.hL.1 h.hK h.hne.symm).trans
      (inf_le_left.trans (uc22p22r_pCoreOf_le_of_isSubnormal h.hyp.hL.1.1))
  have hcomm2 : ⁅L, K⁆ ≤ L ⊔ K :=
    (calC_commutator_le_of_ne h.hyp.hL.1 h.hK h.hne.symm).trans
      (inf_le_left.trans ((CFSG.ClassicalGroups.PCoreSection.pCoreOf_le 2 L).trans le_sup_left))
  have hN : CFSG.Open.pCoreOf 2 D.M ⊓ (L ⊔ K) ≤ CFSG.Open.pCoreOf 2 (L ⊔ K) := by
    refine CFSG.ClassicalGroups.PCoreSection.le_pCoreOf inf_le_right (fun x hx y hy => ?_)
      ((CFSG.ClassicalGroups.PCoreSection.isPGroup_pCoreOf 2 D.M).to_le inf_le_left)
    exact ⟨CFSG.ClassicalGroups.PCoreSection.conj_mem_pCoreOf (hLKleM hx) hy.1,
      (L ⊔ K).mul_mem ((L ⊔ K).mul_mem hx hy.2) ((L ⊔ K).inv_mem hx)⟩
  have hcomm : ⁅L, K⁆ ≤ CFSG.Open.pCoreOf 2 (L ⊔ K) :=
    fun x hx => hN (Subgroup.mem_inf.mpr ⟨hcomm1 hx, hcomm2 hx⟩)
  have h5K : 5 ∣ Nat.card K := by
    have hcard : Nat.card K = Nat.card (Bar2 K) * Nat.card ↥(CFSG.pCore 2 ↥K) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥K)
    rw [hcard, card_bar2_of_isAlt_five h.hKshape]
    exact dvd_mul_of_dvd_left (by norm_num) _
  have hmain := CFSG.GroupTheory.pRank_add_one_le_of_commutator_le_pCoreOf (q := 5)
    (by norm_num) (M := L ⊔ K) (L := L) (X := K) le_sup_left le_sup_right hcomm h.hK.2.1 h5K
  have h5L : 5 ∣ Nat.card L :=
    h.p_eq ▸ ((S17.mem_calLp (D := D) (p := p) (L := L)).mp h.hyp.hL).2.2
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 5 h5L
  have hZ : Nat.card ((Subgroup.zpowers x).map L.subtype) = 5 := by
    rw [Subgroup.card_map_of_injective L.subtype_injective, Nat.card_zpowers, hx]
  have h1 : 1 ≤ CFSG.Open.pRank 5 L :=
    UCK.N588A.one_le_pRank Nat.prime_five (Subgroup.map_subtype_le _) hZ
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
