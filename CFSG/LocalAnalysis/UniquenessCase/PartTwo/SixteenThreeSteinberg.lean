module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SteinbergConjugateBounds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenSix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenEight
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenNine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThirteenB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTwelveB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTwelveD
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Blocks

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s168e3_comm_of_adm (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥)
    (hs3 : s15 D.M V₀ V hV L = 3) {g : G} (hg : s15SixAdm D V g) :
    ⁅V, conjSubgroup V g⁆ = ⊥ := by
  refine s15_Six_reduce D h1217 h.hyp151 hV hL ?_ hg
  intro g' hg'
  by_cases hgM : g' ∈ D.M
  · exact s15_Six_commutator_of_mem D h.hyp151.hyp125 hV hgM
  · refine s15_Six_step2 D h hV hL (by omega) (Or.inl ?_) hgM hg'
    intro hcon
    rw [hs3] at hcon
    omega

theorem s168e3_Eight_not_le_conj (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥)
    (hs3 : s15 D.M V₀ V hV L = 3) {g : G} (hgM : conjSubgroup V g ≤ D.M)
    (hB : ¬ conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) g ≤
      normalizer (wSub V₀ V hV L : Set G)) :
    ¬ V ≤ conjSubgroup D.M g := by
  intro hVg
  have hcomm : ⁅V, conjSubgroup V g⁆ = ⊥ :=
    s168e3_comm_of_adm D h1217 h hV hL hs3 ⟨hVg, hgM⟩
  apply hB
  have hWV : wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L ≤ V :=
    sup_le (preTil_le V₀ V hV _) (s15_Infra_v1Sub_le h.hyp151.hyp125 hV)
  have hBV : conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) g ≤ conjSubgroup V g :=
    E3.conjSubgroup_mono_left g hWV
  have hcomm' : ⁅conjSubgroup V g, V⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact hcomm
  have hBC : conjSubgroup V g ≤ centralizer (V : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).1 hcomm'
  have hWV' : ((wSub V₀ V hV L : Subgroup G) : Set G) ⊆ (V : Set G) :=
    fun x hx => preTil_le V₀ V hV _ hx
  exact hBV.trans (hBC.trans ((Subgroup.centralizer_le hWV').trans
    (Subgroup.centralizer_le_normalizer _)))

theorem s168e3_Eight_core (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥)
    (hs3 : s15 D.M V₀ V hV L = 3) {g : G} (hgM : conjSubgroup V g ≤ D.M) :
    conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) g ≤
      normalizer (wSub V₀ V hV L : Set G) := by
  by_contra hB
  have h151 := h.hyp151
  have h125 := h151.hyp125
  have hVg := s168e3_Eight_not_le_conj D h1217 h hV hL hs3 hgM hB
  set B := conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) g with hBdef
  have hWV : wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L ≤ V :=
    sup_le (preTil_le V₀ V hV _) (s15_Infra_v1Sub_le h125 hV)
  have hBV : B ≤ conjSubgroup V g := E3.conjSubgroup_mono_left g hWV
  have hBM : B ≤ D.M := hBV.trans hgM
  have hB2 : IsPGroup 2 B := (E3.isElemAbelian_conjSubgroup hV g).isPGroup.to_le hBV
  have hlt : B ⊓ normalizer (wSub V₀ V hV L : Set G) < B := by
    refine lt_of_le_of_ne inf_le_left fun heq => hB ?_
    calc B = B ⊓ normalizer (wSub V₀ V hV L : Set G) := heq.symm
      _ ≤ normalizer (wSub V₀ V hV L : Set G) := inf_le_right
  obtain ⟨E, hBE, hEB, hE1⟩ := s15_Glue_exists_hyperplane hB2 hlt
  have hEne : E ≠ B := by
    rintro rfl
    rw [E3.mQuot_self] at hE1
    exact absurd hE1 (by norm_num)
  obtain ⟨v, hvV, hEv, ⟨b, hb, hbv⟩, hvW⟩ :=
    fifteen_seven_G D h151 hV hL hBM hB2 hEB hBE hEne
  have hnotcase : ¬ (s15 D.M V₀ V hV L = 2 ∧
      delta15 D.M V₀ V hV L < gamma15 D.M V₀ V hV L - 1) := by
    rintro ⟨h2, -⟩
    omega
  exact hbv (s15_Eight_fix_of_ne D h hV hL hBdef hgM hVg hEB hE1 hnotcase hvV hEv b hb)

theorem s168e3_wClos_le_normalizer (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥)
    (hs3 : s15 D.M V₀ V hV L = 3) :
    E3.wClos V 0 D.M ≤ normalizer (wSub V₀ V hV L : Set G) :=
  s15_Eight_le_of_core D h1217 h hV hL (fun _g hg => s168e3_Eight_core D h1217 h hV hL hs3 hg)

theorem s168e3_le_conj_of_conj_le (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥)
    (hs3 : s15 D.M V₀ V hV L = 3) {g : G} (hg : conjSubgroup V g ≤ D.M) :
    V ≤ conjSubgroup D.M g :=
  s15_Nine_le_conj D h1217 h hV hL (s168e3_wClos_le_normalizer D h1217 h hV hL hs3) hg

theorem s168e3_wClos_le_centralizer (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥)
    (hs3 : s15 D.M V₀ V hV L = 3) :
    E3.wClos V 0 D.M ≤ centralizer (V : Set G) := by
  refine s15_Glue_wClos_zero_le hV (fun g hgM => ?_)
  have hVg := s168e3_le_conj_of_conj_le D h1217 h hV hL hs3 hgM
  have hcomm : ⁅V, conjSubgroup V g⁆ = ⊥ :=
    s168e3_comm_of_adm D h1217 h hV hL hs3 ⟨hVg, hgM⟩
  have hcomm' : ⁅conjSubgroup V g, V⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact hcomm
  exact fun b hb => (Subgroup.commutator_eq_bot_iff_le_centralizer).1 hcomm' hb

theorem s168e3_normalizer_wClos_le_M (D : Data G) (h127 : R127 D) (h61 : UC6.R6_1 D)
    (hne : D.sig.Nonempty) (hrk : ∀ p ∈ D.sig, 3 ≤ CFSG.pRank p ↥D.M)
    (h1217 : R1217 D) {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L)
    (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥)
    (hs3 : s15 D.M V₀ V hV L = 3) :
    normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
  have hW : E3.wClos V 0 D.T ≤ centralizer (V : Set G) :=
    (E3.wClos_mono (i := 0) D.sylowM.le).trans
      (s168e3_wClos_le_centralizer D h1217 h hV hL hs3)
  exact fifteen_thirteen_a D (r129_1_of_r127 D h127) h61 hne hrk h.hyp151.hyp125 hW

theorem s168e3_centralizer_cClos_le_M (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥)
    (hs3 : s15 D.M V₀ V hV L = 3) (i : ℕ) :
    centralizer (E3.cClos V i D.T : Set G) ≤ D.M := by
  by_contra hC
  have hV1 := s15_Eleven_v1_eq_bot D h hV hC
  have heven := s15_Eleven_even D h hV hL hV1 hC
  rw [hs3] at heven
  obtain ⟨m, hm⟩ := heven
  omega

theorem s168e3_exists_cond1512_at_three {D : Data G} {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hL : IsL3 (lBar V₀ V hV L) 1)
    (hirr : commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ∈
      irrSet (lBar V₀ V hV L))
    (h8 : E3.mQuot
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)) = 8)
    (hs3 : s15 D.M V₀ V hV L = 3) :
    ∃ k : G, Cond1512 D.k D.M V k := by
  have h : Hyp154 D V₀ V L :=
    s168e3_hyp154_of_two_lt_s c hcomp hL hirr h8 (by omega)
  have hV : IsElemAbelian 2 V := h.hyp151.isElemAbelian
  have hN := s168e3_normalizer_wClos_le_M D c.std.h127 c.std.h61 c.std.hx.sig_nonempty
    (fun p hp => by rw [UC6.groupPRank_eq_pRank]; exact c.std.hSg.three_le p hp) c.std.h1217 h hV c.ne hs3
  have hC := s168e3_centralizer_cClos_le_M D h hV c.ne hs3 D.k
  obtain ⟨H, A, K, hS, hA, hK, hne⟩ :=
    s15_Thirteen_exists_A_K D c.std.h126 h.hyp151.hyp125 hN hC
  have hgamma := s168e3_st8_gamma_eq_eight D hL hirr h8
  have hkm : D.k < max (gamma15 D.M V₀ V hV L)
      ((s15 D.M V₀ V hV L - 2) * gamma15 D.M V₀ V hV L) := by
    rcases s15_Thirteen_k_cases D with hk | hk <;> rw [hk, hgamma, hs3] <;> norm_num
  have hr := s15_Thirteen_lt_rParam D h hV c.ne hkm
  have hbeta : (D.k : ℕ∞) < betaN 0 D.M V :=
    lt_of_lt_of_le (by exact_mod_cast hkm) (s15_Thirteen_beta D c.std.h1217 h hV c.ne)
  have hO2 := s15_Thirteen_six_nine D h.hyp151.hyp125 hS hA hK hr hbeta hne
  have hO : (calO D.k D.M V₀ V).Nonempty := hO2.mono fun X hX => by
    obtain ⟨g, rfl, hIn⟩ := hX
    exact ⟨g, rfl, hIn.1⟩
  exact exists_cond1512 hO


theorem case163_1_of_l3_two_rank_eight_of_ne_three {D : Data G} {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hL : IsL3 (lBar V₀ V hV L) 1)
    (hirr : commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ∈
      irrSet (lBar V₀ V hV L))
    (h8 : E3.mQuot
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)) = 8)
    (hnot3 : s15 D.M V₀ V hV L ≠ 3) :
    Case163_1 D V₀ V hV L := by
  refine ⟨hL, s168e3_st8_gamma_eq_eight D hL hirr h8, ?_⟩
  have h1 : 1 < s15 D.M V₀ V hV L := s168e3_one_lt_s c hcomp hL hirr h8
  have hle : s15 D.M V₀ V hV L ≤ 3 := s168e3_s_le_three c hcomp hL
  omega


theorem s168e3_twelve_kernel_data {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hL : IsL3 (lBar V₀ V hV L) 1)
    (hirr : commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ∈
      irrSet (lBar V₀ V hV L))
    (h8 : E3.mQuot
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)) = 8)
    (hs3 : s15 D.M V₀ V hV L = 3) :
    ∃ (a : G) (Y C : Subgroup G),
      Cond1512 D.k D.M V a ∧
      Y = ySub15 D.M V₀ V hV L (wSub V₀ V hV L) a ∧
      C ≤ Y ∧ IsPGroup 2 Y ∧ 6 ≤ E3.mQuot Y C ∧
      Y ≤ normalizer (wSub V₀ V hV L : Set G) ∧ Y ≤ stabTil V₀ V ∧
      (∀ y ∈ Y, y ∈ C ↔
        ∀ f ∈ wSub V₀ V hV L, y * f * y⁻¹ * f⁻¹ ∈ V₀) := by
  obtain ⟨a, ha⟩ := s168e3_exists_cond1512_at_three c hcomp hL hirr h8 hs3
  have h : Hyp154 D V₀ V L :=
    s168e3_hyp154_of_two_lt_s c hcomp hL hirr h8 (by omega)
  have hVcan : IsElemAbelian 2 V := h.hyp151.isElemAbelian
  have hV1 : v1Sub D.M V₀ V hV L = V₀ := s168e3_st8_v1_eq D hL hirr h8
  have hgamma : gamma15 D.M V₀ V hV L = 8 := s168e3_st8_gamma_eq_eight D hL hirr h8
  let W : Subgroup G := wSub V₀ V hV L
  let Y : Subgroup G := ySub15 D.M V₀ V hV L W a
  have hV0V : V₀ ≤ V := h.hyp151.hyp125.pairFacts.le
  have hV0W : V₀ ≤ W := by
    intro x hx
    change x ∈ wSub V₀ V hV L
    rw [wSub, mem_preTil_iff_of_mem _ _ _ _ (hV0V hx)]
    have hx1 : mkTil V₀ V hV (IntMod.mk hV ⟨x, hV0V hx⟩) = 1 := by
      rw [mkTil, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_modNull]
      exact hx
    simp [hx1]
  have hFW : fSub15 D.M V₀ V hV L W = W := by
    rw [fSub15, hV1]
    exact sup_eq_left.mpr hV0W
  have hXmem : W ∈ wConj D.M V₀ V hV L :=
    ⟨1, D.M.one_mem, by
      change wSub V₀ V hV L = conjSubgroup (wSub V₀ V hV L) 1
      simp [conjSubgroup_one]⟩
  have hn2 : D.k ≤ 2 := by
    rcases s15_Thirteen_k_cases D with hk | hk <;> omega
  have hbound := (s15_Twelve_rank_bound D h hVcan ha hXmem).1
  have hcY : E3.mQuot V (centralizer (Y : Set G)) < gamma15 D.M V₀ V hV L := by
    change E3.mQuot V (centralizer (ySub15 D.M V₀ V hV L W a : Set G)) <
      gamma15 D.M V₀ V hV L
    rw [hgamma]
    omega
  have hYnorm : Y ≤ normalizer (W : Set G) :=
    (s15_Twelve_fixes D c.std.h1217 h.hyp151 hVcan c.ne
      (by change ySub15 D.M V₀ V hV L W a ≤ D.M; exact inf_le_right) hcY hXmem).2
  have hYstab : Y ≤ stabTil V₀ V :=
    (by change ySub15 D.M V₀ V hV L W a ≤ D.M; exact inf_le_right : Y ≤ D.M).trans c.m_le_stabTil
  have ha' : Cond1512 D.k D.M V a⁻¹ := cond1512_inv ha
  have hbound' := (s15_Twelve_rank_bound D h hVcan ha' hXmem).1
  have hcY' : E3.mQuot V (centralizer (ySub15 D.M V₀ V hV L W a⁻¹ : Set G)) <
      gamma15 D.M V₀ V hV L := by
    rw [hgamma]
    omega
  have hZk : ¬ fSub15 D.M V₀ V hV L W ≤ conjSubgroup D.M a := by
    intro hle
    have hin : conjSubgroup (fSub15 D.M V₀ V hV L W) a⁻¹ ≤ D.M := by
      have h1 := E3.conjSubgroup_mono_left a⁻¹ hle
      rwa [conjSubgroup_conjSubgroup_inv] at h1
    exact s15_Twelve_whole D c.std.h1217 h hVcan c.ne ha' hXmem hin hcY'
  obtain ⟨C, hCY, hCchar, hCm, hCbound⟩ :=
    s15_Twelve_kernel D h hVcan ha hXmem hXmem hZk
  have hYV : Y ≤ conjSubgroup V a := by
    have h1 : Y ≤ conjSubgroup (fSub15 D.M V₀ V hV L W) a := by
      change ySub15 D.M V₀ V hV L W a ≤ conjSubgroup (fSub15 D.M V₀ V hV L W) a
      exact inf_le_left
    rw [hFW] at h1
    exact h1.trans (E3.conjSubgroup_mono_left a (preTil_le V₀ V hV _))
  have hY2 : IsPGroup 2 Y :=
    (E3.isElemAbelian_conjSubgroup hVcan a).isPGroup.to_le hYV
  have hC6 : 6 ≤ E3.mQuot Y C := by
    change 6 ≤ E3.mQuot (ySub15 D.M V₀ V hVcan L W a) C
    have := hCbound
    rw [hgamma] at this
    omega
  have hCchar0 : ∀ y ∈ Y, y ∈ C ↔
      ∀ f ∈ fSub15 D.M V₀ V hV L W, y * f * y⁻¹ * f⁻¹ ∈ v1Sub D.M V₀ V hV L :=
    hCchar
  have hCcharW : ∀ y ∈ Y, y ∈ C ↔
      ∀ f ∈ W, y * f * y⁻¹ * f⁻¹ ∈ V₀ := by
    intro y hy
    rw [hCchar0 y hy]
    constructor
    · intro hc f hf
      have hf' : f ∈ fSub15 D.M V₀ V hV L W := by rwa [hFW]
      have := hc f hf'
      rwa [hV1] at this
    · intro hc f hf
      have hfW : f ∈ W := by rwa [hFW] at hf
      have := hc f hfW
      rwa [hV1]
  exact ⟨a, Y, C, ha, rfl, hCY, hY2, hC6, hYnorm, hYstab, hCcharW⟩



theorem s168e3_s_ne_three {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hL : IsL3 (lBar V₀ V hV L) 1)
    (hirr : commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ∈
      irrSet (lBar V₀ V hV L))
    (h8 : E3.mQuot
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)) = 8)
    (hs3 : s15 D.M V₀ V hV L = 3) :
    False := by
  obtain ⟨a, Y, C, ha, hYeq, hCY, hY2, hC6, hYN, hYs, hCchar⟩ :=
    s168e3_twelve_kernel_data c hcomp hL hirr h8 hs3
  set W : Subgroup G := wSub V₀ V hV L with hW
  set U : Subgroup (Vtil V₀ V hV) := wTil V₀ V hV L with hU
  let B : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV Y
  have hYleM : Y ≤ D.M := by
    rw [hYeq]
    exact inf_le_right
  have himg : imgTil V₀ V hV W = U := by
    rw [hW, hU, wSub, imgTil_preTil]
  have hBU : B ≤ stabSub U := by
    have hle := s15_LP_barSub_le_stabSub_imgTil (V₀ := V₀) (V := V)
      (B := Y) (U := W) hV hYs hYN
    rwa [himg] at hle
  have hBA : B ≤ Mbar D.M V₀ V hV :=
    barSub_mono V₀ V hV hYleM
  obtain ⟨t, hc⟩ := s168e3_exists_H5Cfg c hcomp hL
  have hBN : B ≤ normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) := by
    intro b hb
    obtain ⟨g, hgY, rfl⟩ := (mem_barSub V₀ V hV Y b).1 hb
    have hbB : actTil V₀ V hV g ∈ B := actTil_mem_barSub V₀ V hV hgY g.2
    exact s16h_bl_mem_normalizer_of_stab hc.conc (hBA hbB) (hBU hbB)
  have hdiv : Nat.card (autSub B U) ∣ 336 :=
    s16h_H5_rowSt8_autSub_card_dvd hc ⟨hL, h8⟩ hirr hBN
  let f : ↥Y →* MulAut (Vtil V₀ V hV) :=
    (actTil V₀ V hV).comp (Subgroup.inclusion hYs)
  let fU : ↥Y →* ↥(stabSub U) :=
    f.codRestrict (stabSub U) (fun y =>
      hBU (actTil_mem_barSub V₀ V hV y.2 (hYs y.2)))
  let rho : ↥Y →* MulAut U := (resHom U).comp fU
  have hrange_le : rho.range ≤ autSub B U := by
    rintro φ ⟨y, rfl⟩
    rw [mem_autSub]
    refine ⟨fU y, ?_, rfl⟩
    exact actTil_mem_barSub V₀ V hV y.2 (hYs y.2)
  have hker : rho.ker = C.subgroupOf Y := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h1
      rw [hCchar (y : G) y.2]
      intro f0 hf0
      have hf0' : f0 ∈ preTil V₀ V hV (wTil V₀ V hV L) := by rwa [hW] at hf0
      have hf0V : f0 ∈ V := preTil_le V₀ V hV (wTil V₀ V hV L) hf0'
      have hq : mkTil V₀ V hV (IntMod.mk hV ⟨f0, hf0V⟩) ∈ U := by
        rw [← himg]
        exact (mem_imgTil V₀ V hV W _).2
          ⟨IntMod.mk hV ⟨f0, hf0V⟩, hf0, rfl⟩
      have hfix := congrArg (fun φ : MulAut U => (φ ⟨mkTil V₀ V hV
        (IntMod.mk hV ⟨f0, hf0V⟩), hq⟩ : Vtil V₀ V hV)) h1
      have hfix' : actTil V₀ V hV ((Subgroup.inclusion hYs) y)
          (mkTil V₀ V hV (IntMod.mk hV ⟨f0, hf0V⟩)) =
          mkTil V₀ V hV (IntMod.mk hV ⟨f0, hf0V⟩) := by
        simpa [rho, fU, f, resHom_apply, MulAut.one_apply] using hfix
      rw [actTil_mk, mkTil_eq_iff, actStab_apply_val, Subgroup.coe_inclusion] at hfix'
      simp only [IntMod.val, IntMod.mk] at hfix'
      simpa [mul_assoc] using hfix'
    · intro hmem
      have hcent : (fU y : MulAut (Vtil V₀ V hV)) ∈ centSub U := by
        rw [mem_centSub]
        intro q hq
        have hq' : q ∈ imgTil V₀ V hV W := by simpa [← himg] using hq
        obtain ⟨x, hxW, rfl⟩ := (mem_imgTil V₀ V hV W q).1 hq'
        have hcomm := (hCchar (y : G) y.2).1 hmem x.val hxW
        have hcomm' : (y : G) * x.val * (y : G)⁻¹ * x.val⁻¹ ∈ V₀ := by
          simpa [mul_assoc] using hcomm
        have hfix : actTil V₀ V hV ((Subgroup.inclusion hYs) y)
            (mkTil V₀ V hV x) = mkTil V₀ V hV x := by
          rw [actTil_mk, mkTil_eq_iff, actStab_apply_val, Subgroup.coe_inclusion]
          simpa [mul_assoc] using hcomm'
        have hxU : mkTil V₀ V hV x ∈ U := by
          rw [← himg]
          exact (mem_imgTil V₀ V hV W _).2 ⟨x, hxW, rfl⟩
        have hres : resHom U (fU y) ⟨mkTil V₀ V hV x, hxU⟩ =
            ⟨mkTil V₀ V hV x, hxU⟩ := by
          apply Subtype.ext
          rw [resHom_apply]
          exact hfix
        have hres' := congrArg (fun z : U => (z : Vtil V₀ V hV)) hres
        simpa [rho, fU, f, resHom_apply, Subgroup.coe_inclusion] using hres'
      have hres : (resHom U) (fU y) = 1 := by
        rw [← MonoidHom.mem_ker, ker_resHom U, Subgroup.mem_subgroupOf]
        exact hcent
      simpa [rho] using hres
  have hcard : Nat.card rho.range = 2 ^ E3.mQuot Y C := by
    rw [← E3.relIndex_eq_two_pow hY2 C]
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  have hrange_dvd : Nat.card rho.range ∣ 336 :=
    (Subgroup.card_dvd_of_le hrange_le).trans hdiv
  have hpow : 2 ^ 6 ∣ Nat.card rho.range := by
    rw [hcard]
    exact pow_dvd_pow 2 hC6
  have h64 : (2 : ℕ) ^ 6 ∣ 336 := hpow.trans hrange_dvd
  norm_num at h64



theorem case163_1_of_l3_two_rank_eight {D : Data G} {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hL : IsL3 (lBar V₀ V hV L) 1)
    (hirr : commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ∈
      irrSet (lBar V₀ V hV L))
    (h8 : E3.mQuot
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)) = 8) :
    Case163_1 D V₀ V hV L := by
  refine ⟨hL, s168e3_st8_gamma_eq_eight D hL hirr h8, ?_⟩
  have h1 : 1 < s15 D.M V₀ V hV L := s168e3_one_lt_s c hcomp hL hirr h8
  have hle : s15 D.M V₀ V hV L ≤ 3 := s168e3_s_le_three c hcomp hL
  have hne : s15 D.M V₀ V hV L ≠ 3 := fun hs3 =>
    s168e3_s_ne_three c hcomp hL hirr h8 hs3
  omega


end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
