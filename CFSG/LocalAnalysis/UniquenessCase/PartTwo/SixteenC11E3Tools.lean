module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3Ctx
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11DimD
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11RouteF
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.MbarSigmaRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

theorem s1611e3_exists_noncyclic_mbar {D : Data G} (h : S1611e3Std D) {V₀ V : Subgroup G}
    (h16 : Hyp16 D V₀ V) {p : ℕ} (hp : p ∈ D.sig) :
    ∃ P : Subgroup (MulAut (Vtil V₀ V h16.hyp125.isElemAbelian)),
      P ≤ Mbar D.M V₀ V h16.hyp125.isElemAbelian ∧ IsPGroup p ↥P ∧ ¬ IsCyclic ↥P := by
  have h125 : Hyp125 D V₀ V := h16.hyp125
  have hpp : p.Prime := (D.sig_prime p hp).1
  have h2 : 2 ≤ CFSG.Open.pRank p (Mbar D.M V₀ V h125.isElemAbelian) :=
    S17.two_le_pRank_mbar_of_mem_sig h125 h.hx h.h61 h.h127 (c23_card_v0_le_four D h16) hp
  obtain ⟨E, hEM, hE, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank hpp.one_lt (Mbar D.M V₀ V h125.isElemAbelian)
  exact ⟨E, hEM, hE.isPGroup, s16c11_not_isCyclic_of_exponent hpp (fun x hx => hE.2 x hx)
    (by rw [hEcard]; exact pow_dvd_pow p h2)⟩

theorem s1611e3_tiConj_of_pRank_lt {D : Data G} (h : S1611e3Std D) {V₀ V : Subgroup G}
    (h16 : Hyp16 D V₀ V) {p : ℕ} (hp : p ∈ D.sig)
    (hlt : CFSG.Open.pRank p (Mbar D.M V₀ V h16.hyp125.isElemAbelian) < 3) :
    S16C11TI D V₀ V := by
  have h125 : Hyp125 D V₀ V := h16.hyp125
  have hP := h125.pairFacts
  have hpp : p.Prime := (D.sig_prime p hp).1
  have hp2 : p ≠ 2 := (D.sig_prime p hp).2
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M :=
    h.hSg.sig1_sp p (h.h1219 V₀ V h125 ▸ hp)
  have h4 : Nat.card V₀ ≤ 4 := c23_card_v0_le_four D h16
  have hK : p ∣ Nat.card ↥(F11.CTilde D.M V₀ V) := by
    by_contra hnd
    have h1 := pRank_le_pRank_mbar_of_not_dvd h125.isElemAbelian hP hpp hnd
    have h3 := h.hx.three_le p hp
    omega
  exact s16c11_tiConj_of_stronglyEmbedded D h125 hsp fun _ w hw hw0 =>
    s16c11_dvd_card_cent_of_dvd_cTilde D (Hyp125.hyp11 h.h127 h125) h4 hpp hp2 hK hw hw0

theorem s1611e3_tiConj_of_bot (D : Data G) (V : Subgroup G) : S16C11TI D ⊥ V := by
  intro g _
  exact ⟨bot_inf_eq _, by simp [conjSubgroup]⟩

theorem s1611e3_tiConj_of_dvd {D : Data G} (h : S1611e3Std D) {V₀ V : Subgroup G}
    (h16 : Hyp16 D V₀ V) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded q D.M)
    (hK : q ∣ Nat.card ↥(F11.CTilde D.M V₀ V)) : S16C11TI D V₀ V :=
  s16c11_tiConj_of_stronglyEmbedded D h16.hyp125 hsp fun _ w hw hw0 =>
    s16c11_dvd_card_cent_of_dvd_cTilde D (Hyp125.hyp11 h.h127 h16.hyp125)
      (c23_card_v0_le_four D h16) hq hq2 hK hw hw0

@[expose] def S1611e3RouteF (D : Data G) (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) (p : ℕ) :
    Prop :=
  ∃ Xbar : Subgroup (MulAut (Vtil V₀ V hV)), Xbar ≤ Mbar D.M V₀ V hV ∧
    barSub V₀ V hV D.T ≤ Xbar ∧ Group.IsSolvable ↥Xbar ∧
    (∀ x ∈ Xbar, (∃ n : ℕ, x ^ p ^ n = 1) → x ^ p = 1) ∧
    padicValNat p (Nat.card ↥(Xbar ⊓ centSub (fixV (barSub V₀ V hV D.T)))) + 2 ≤
      padicValNat p (Nat.card ↥Xbar)

theorem s1611e3_two_add_lt_rMV {D : Data G} (h : S1611e3Std D) {V₀ V : Subgroup G}
    (h125 : Hyp125 D V₀ V) (hm3 : 3 ≤ mBar D.M V₀ V h125.isElemAbelian) :
    ((2 + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V := by
  by_cases hV₀ : V₀ = ⊥
  · subst hV₀
    have hV1 : InCalV1 D.M D.T V := by
      rcases h125.1 with ⟨hW, -⟩ | ⟨hV0, -⟩
      · exact hW.1.1
      · exact absurd rfl hV0.1.1
    have hm2 : MBarGT D.M ⊥ V 2 :=
      (h125.mBarGT_iff_lt_mBar 2).2 (lt_of_lt_of_le (by norm_num : 2 < 3) hm3)
    have h2 : (2 : ℕ∞) < rMV D.M V :=
      h.h111 D.M V (D.T ⊓ centralizer (V : Set G)) (TwelveShort.setting11_of_inCalV1 D hV1)
        hm2 2 hm2
    simpa [mSub, rk_bot] using h2
  · have hW : WeakClosureSetting D V₀ V :=
      weakClosureSetting_of_hyp125 D h.hx h.h61 h.h127 h.h1114 h125 hV₀
    have hm1 : 1 < mBar D.M V₀ V h125.isElemAbelian :=
      lt_of_lt_of_le (by norm_num : 1 < 3) hm3
    have h1 := h.h162 D V₀ V hW h.hx h.h61 hV₀ hm1
    refine lt_of_lt_of_le ?_ h1
    exact_mod_cast (by omega : 2 + mSub V₀ < mBar D.M V₀ V h125.isElemAbelian + mSub V₀)

theorem s1611e3_normalizer_le_of_dimD {D : Data G} (h : S1611e3Std D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV)
    (hTI : S16C11TI D V₀ V) (hm3 : 3 ≤ mBar D.M V₀ V hV) (hD1 : S16C11DimD1 D V₀ V hV)
    (hD2 : S16C11DimD2 D V₀ V hV) {p : ℕ} (hp : p ∈ D.sig) :
    normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
  classical
  have h16 : Hyp16 D V₀ V := hc.setting.hyp16
  have h125 : Hyp125 D V₀ V := h16.hyp125
  have hm : MBarGT D.M V₀ V 1 := (h125.mBarGT_iff_lt_mBar 1).2 (lt_of_lt_of_le (by norm_num) hm3)
  have hr := s1611e3_two_add_lt_rMV h h125 (hm3.trans (le_of_eq rfl))
  have hβ : (2 : ℕ∞) < betaN 0 D.M V := by
    have h1 := succ_le_deltaN_of_mBarGT D h125
      ((h125.mBarGT_iff_lt_mBar 2).2 (lt_of_lt_of_le (by norm_num) hm3)) 0
    exact lt_of_lt_of_le (by exact_mod_cast (by norm_num : 2 < 2 + 1))
      (h1.trans (deltaN_le_betaN 0))
  obtain ⟨P, hPM, hPp, hPc⟩ := s1611e3_exists_noncyclic_mbar h h16 hp
  exact s16c11_normalizer_le_of_dimD D h.h61 hV h125 hTI hm hr hβ hD1 hD2 hp hPM hPp hPc

theorem s1611e3_normalizer_le_of_two_rank {D : Data G} (h : S1611e3Std D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV)
    (hTI : S16C11TI D V₀ V) (h2 : CFSG.Open.pRank 2 (Mbar D.M V₀ V hV) ≤ 2)
    (hm3 : 3 ≤ mBar D.M V₀ V hV) {p : ℕ} (hp : p ∈ D.sig) :
    normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
  have hD1 : S16C11DimD1 D V₀ V hV := by
    intro E hE _ hmE
    have hle : rk ↥E ≤ CFSG.Open.pRank 2 (Mbar D.M V₀ V hV) := H.rk_le_pRank hE.1 hE.2.2.1
    have hge : 3 ≤ rk ↥E := le_trans hm3 hmE
    exact absurd (hle.trans h2) (by omega)
  have hD2 : S16C11DimD2 D V₀ V hV := by
    intro E hE
    have hne : E ≠ ⊥ := hE.2.1
    have hmq : E3.mQuot E ⊥ < 3 := by
      rw [E3.mQuot_bot_eq_rk]
      exact lt_of_le_of_lt ((H.rk_le_pRank hE.1 hE.2.2.1).trans h2) (by norm_num)
    have hfix0 : fixV (⊥ : Subgroup (MulAut (Vtil V₀ V hV))) = fixV E :=
      hE.2.2.2 ⊥ bot_le hmq
    have hfix : fixV E = ⊤ := by rw [← hfix0, B1.fixV_bot]
    exact fun _ => hne (B1.eq_bot_of_fixV_eq_top hfix)
  exact s1611e3_normalizer_le_of_dimD h hc hTI hm3 hD1 hD2 hp

section Certified


theorem s1611e3_normalizer_le_of_routeA_empty {D : Data G} (h : S1611e3Std D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV)
    (hTI : S16C11TI D V₀ V)
    (hA : ∀ E ∈ calABar 2 D.M V₀ V hV, ¬ E ≤ barSub V₀ V hV D.T) {p : ℕ} (hp : p ∈ D.sig) :
    normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
  classical
  have h16 : Hyp16 D V₀ V := hc.setting.hyp16
  have h125 : Hyp125 D V₀ V := h16.hyp125
  have hk1 : 1 ≤ D.k := TwelveShort.one_le_k D
  have hm : MBarGT D.M V₀ V 1 :=
    (h125.mBarGT_iff_lt_mBar 1).2 (lt_of_le_of_lt hk1 (h.out10 hc).1)
  have hr : ((1 + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V :=
    lt_of_le_of_lt (by exact_mod_cast Nat.add_le_add_right hk1 _)
      (s16n9b_k_add_lt_rMV D h.hSg (h.h1219 V₀ V h125) h.hx h.h61 h.h127 h16)
  have hγ : V₀ = ⊥ ∨ ((1 + mSub V₀ : ℕ) : ℕ∞) < gammaN 1 D.M V := by
    by_cases h0 : V₀ = ⊥
    · exact Or.inl h0
    · exact Or.inr (s16c11_one_add_lt_gammaN_one hk1
        (s16n9b_main_gamma D h.hSg (h.h1219 V₀ V h125) h.h1217 hV hc h0))
  have hbot : ∀ A ∈ E3.gammaSet V 0 D.T, barSub V₀ V hV A = ⊥ := by
    intro A hA'
    rcases s16c11_barSub_gammaSet_zero_eq_bot_or_mem D hV h125 hm hr hγ
      (fun g hg _ _ => hTI g hg) hA' with h0 | hmem
    · exact h0
    · exact absurd (barSub_mono V₀ V hV hA'.1) (hA _ hmem)
  obtain ⟨P, hPM, hPp, hPc⟩ := s1611e3_exists_noncyclic_mbar h h16 hp
  exact s16c11_normalizer_le_of_forall_barSub_eq_bot D h.h61 hV h125 hbot hp hPM hPp hPc

theorem s1611e3_normalizer_le_of_routeF_data {D : Data G} (h : S1611e3Std D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) {p : ℕ}
    (hp : p ∈ D.sig) (hR : S1611e3RouteF D V₀ V hV p) :
    normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
  obtain ⟨X, hXM, hTX, hsolv, hexp, hcount⟩ := hR
  have h125 : Hyp125 D V₀ V := hc.setting.hyp16.hyp125
  exact s16c11_normalizer_le_of_routeF D h.h61 (h.r16_10_2 h125) (h.r16_9 h125) hV hc hp hXM hTX
    hsolv hexp hcount

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
