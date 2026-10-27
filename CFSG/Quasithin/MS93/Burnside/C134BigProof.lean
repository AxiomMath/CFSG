module

public import CFSG.Quasithin.MS93.Burnside.C134
public import CFSG.Quasithin.MS93.Burnside.C134Big
import CFSG.Quasithin.MS93.MResC13
public import CFSG.Quasithin.MS93.ASC134C5
public import CFSG.Quasithin.MS93.ASC134NC5
public import CFSG.Quasithin.MS93.Burnside.D468Base
public import CFSG.Quasithin.MS93.Burnside.RigMain
public import CFSG.Quasithin.MS93.MS93FrontierDeep

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S45
open scoped commutatorElement Matrix

section Field

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem burnsideC134w_four_le_card_of_via (h : PUHyp M T L) (hL : ¬ MRes.NotSL3Big L)
    {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ) :
    4 ≤ Fintype.card F := by
  obtain ⟨⟨n, hn⟩, hφs, -⟩ := hφ
  have hα : Function.Surjective (φ.comp (Subgroup.inclusion h.L_le)) := fun y => by
    obtain ⟨ℓ, hℓL, hℓ⟩ := exists_mem_L_eq h hφs y
    exact ⟨⟨ℓ, hℓL⟩, hℓ⟩
  have hmod := MRes.isModO2Surj_of_surjective h hn hα
  have h2 : Fintype.card F ≠ 2 := fun h2 => hL (MRes.notSL3Big_of_isModO2Surj_two h2 hmod)
  have h1 : 1 < Fintype.card F := Fintype.one_lt_card
  rw [hn] at h1 h2 ⊢
  rcases n with _ | _ | n
  · simp at h1
  · simp at h2
  · calc 4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ (n + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

end Field

section Ctx

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F] {M T L : Subgroup G}
  {φ : ↥M →* ↥(StatedSL 3 F)}

theorem burnsideC134w_hC1_of_four (h14 : MS14AS) (hSQ : SQTKQuot) (c : Ctx M T L φ)
    (hZV : c.HZV) (hq : 4 ≤ Fintype.card F) {p : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ}
    (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a) (h34 : 34 ≤ a) (haN : a + 30 ≤ N) :
    ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ ⊓ Zloc c.hyp.le L (p a) ≤
      Hloc c.hyp.le L (p a) := by
  by_cases hZH : Zloc c.hyp.le L (p a) ≤ Hloc c.hyp.le L (p a)
  · exact inf_le_right.trans hZH
  have hα := c.isMVtx_of_isGoodPath hp (k := a) (by omega) ha
  exact EmptyFaithful.Stellmacher.MS93Support.commutator_inf_zloc_le_hloc c hα
    (EmptyFaithful.Stellmacher.MS93Support.s45C1aQ4_holds G M T L F φ c hq (p a) hα)
    (EmptyFaithful.Stellmacher.MS93Support.burnsideRig_s45C1bQ4 h14 hSQ G M T L F φ c hZV hq
      p N hp a ha h34 haN hZH)

theorem burnsideC134w_hC14_of_four (h14 : MS14AS) (hSQ : SQTKQuot) (c : Ctx M T L φ)
    (hZV : c.HZV) (hq : 4 ≤ Fintype.card F) : c.HC14 :=
  fun _ _ hp _ ha h34 haN => ⟨burnsideC134w_hC1_of_four h14 hSQ c hZV hq hp ha h34 haN,
    S45R.Ctx.not_frattiniIn_le c h14 hSQ hZV hp ha h34 haN⟩

theorem burnsideC134w_hQ2b_of_four (h14 : MS14AS) (hSQ : SQTKQuot) (c : Ctx M T L φ)
    (hZV : c.HZV) (hq : 4 ≤ Fintype.card F) : c.HQ2b := by
  intro p p' N hp hp' a ha h34 haN hpp' hU1 hU3
  have hQ4 := S45Q4.hQ4 c
  obtain ⟨hC1, hC4⟩ := burnsideC134w_hC14_of_four h14 hSQ c hZV hq p N hp a ha h34 haN
  exact ⟨c.inf_centralizer_ltil_le h14 hSQ hZV hQ4 hp hp' ha h34 haN hpp' hU1 hU3 hC1,
    c.center_le_uloc_sup_hloc h14 hSQ hZV hQ4 hp hp' ha h34 haN hpp' hU1 hU3 hC1,
    c.frattiniIn_eq_vcirc h14 hSQ hZV hQ4 hp hp' ha h34 haN hpp' hU1 hU3 hC1 hC4,
    c.inf_centralizer_vcirc_le_whv h14 hSQ hZV hQ4 hp hp' ha h34 haN hpp' hU1 hU3,
    c.commutator_qv_ltil_le_top hZV hp hp' ha h34 haN hpp' hU3⟩

end Ctx

@[expose] def burnsideC134w_S45Big : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → 4 < critDist (puAmalgam h.le) → IsSL3Full M T L → ¬ MRes.NotSL3Big L →
      MS93Case13 (Vq M L) T L

theorem burnsideC134w_s45Big_of (h43 : S43) (h44 : S44) (h14 : MS14AS) (hSQ : SQTKQuot) :
    burnsideC134w_S45Big := by
  intro G _ _ M T L h hmin hb hfull hL
  obtain ⟨F, _, _, φ, hφ⟩ := isSL3Full_iff_exists_via.mp hfull
  have hq := burnsideC134w_four_le_card_of_via h hL hφ
  have c : Ctx M T L φ := Ctx.ofItems h43 h44 h hmin hb hφ
  have hZV : c.HZV := c.hZV_of_ne_two (by omega)
  obtain ⟨p, hp⟩ := c.exists_isGoodPath_of_ctx 28
  have hα := c.isMVtx_of_isGoodPath hp (k := 34) (by omega) (by decide)
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isMVtx _ hα (isMVtx_baseA _)
  obtain ⟨ψ₀, hψ₀, hU₀, hHc, hF4, hF3, hZL, h₁, h₂, h₃⟩ :=
    c.exists_case13_of_isGoodPath h14 hSQ hZV (burnsideC134w_hQ2b_of_four h14 hSQ c hZV hq)
      (hp.smul g) (by omega) hg
  have hab := adj_baseA_baseB (puAmalgam h.le)
  have hA := isMVtx_baseA (puAmalgam h.le)
  have hT : (pCoreOf 2 M).relIndex T = Fintype.card F ^ 2 := by
    have := c.relIndex_qv hA hab
    rwa [puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le, puAmalgam.qv_baseB,
      S46.relIndex_imM h.le h.le] at this
  have hU : (Uq M T L ⊓ Subgroup.centralizer (T : Set G)).relIndex (Uq M T L) =
      Fintype.card F := by
    have := c.relIndex_zh hA hab
    rwa [puAmalgam.zh_baseB, puAmalgam.zm_baseA, S46.relIndex_imM h.le (normalClosureIn_le _ _),
      ← S46.relIndex_Uq_inf_centralizer h hφ] at this
  have hHZ : Hloc h.le L (baseA _) ≤ Zloc h.le L (baseA _) :=
    (Subgroup.commutator_mono (c.vcirc_le_vv _) le_rfl).trans (c.commutator_vv_qv_le_zloc hA)
  exact case13_of_baseA h hφ hT hU hψ₀ hU₀ hHc hHZ hF4 hF3 hZL h₁ h₂ h₃

@[expose] def burnsideC134w_MS93ASBig : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G), PUHyp M T L → ¬ MRes.NotSL3Big L →
    MS93ConclAS M T L

section Assembly

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem burnsideC134w_ms93ConclAS_of_endConcl (h38 : S38) (h45 : burnsideC134w_S45Big)
    (h46 : S46) (h512 : S512) (h7 : S7Two) (h : PUHyp M T L) (hL : ¬ MRes.NotSL3Big L)
    (hb : 2 < critDist (puAmalgam h.le)) (he : S34D.EndConcl T L) : MS93ConclAS M T L := by
  obtain ⟨M₁, T₁, h₁, hT₁T, hmin₁, hor⟩ := he
  have hV₁ : Vq M₁ L = Vq M L := h.vq_eq_vq h₁
  have hpos₁ := h₁.critDist_pos
  obtain ⟨m, hm⟩ := h₁.critDist_even
  by_cases hb₁ : critDist (puAmalgam h₁.le) = 2
  · have h5 := h7 G M T L M₁ T₁ h h₁ hT₁T hmin₁ hV₁ hb hb₁
    have hX : Xq M ≤ Zq M L ⊔ Uq M T L := by
      rcases h38 G M T L h hb with hSL | hSp
      · exact hSL.1.le
      · exact (case5_sp4U_false h h5 hSp).elim
    exact MS93ConclAS.of_case5 hX h5
  have hgood := hor.resolve_left hb₁
  have hb₁' : 2 < critDist (puAmalgam h₁.le) := by omega
  rcases h38 G M₁ T₁ L h₁ hb₁' with hSL₁ | hSp₁
  swap
  · exact (h512 G M₁ T₁ L h₁ hmin₁ hb₁' (hgood.2 hSp₁)).elim
  have hX : Xq M ≤ Zq M L ⊔ Uq M T L := by
    rcases h38 G M T L h hb with hSL | hSp
    · exact hSL.1.le
    · exact (sl3U_sp4U_false h h₁ hSL₁ hSp).elim
  have hFull := hgood.1 hSL₁
  rcases (show critDist (puAmalgam h₁.le) = 4 ∨ 4 < critDist (puAmalgam h₁.le) by omega)
    with h4 | h4
  · have h11 := h46 G M₁ T₁ L h₁ hmin₁ h4 hFull
    rw [hV₁] at h11
    exact MS93ConclAS.of_case11 hX (h11.mono hT₁T)
  · have h13 := h45 G M₁ T₁ L h₁ hmin₁ h4 hFull hL
    rw [hV₁] at h13
    exact MS93ConclAS.of_case13 hX (h13.mono hT₁T)

end Assembly

theorem burnsideC134w_ms93ASBig_of (h32 : S32) (h36 : S36) (h37 : S37) (h18 : S18) (h38 : S38)
    (h45 : burnsideC134w_S45Big) (h46 : S46) (h512 : S512) (h7 : S7Two)
    (hend : S34D.S34DEnd) : burnsideC134w_MS93ASBig := by
  intro G _ _ M T L h hL
  by_cases hb : critDist (puAmalgam h.le) = 2
  · exact ms93ConclAS_of_critDist_eq_two h32 h36 h37 h18 h hb
  · have hpos := h.critDist_pos
    obtain ⟨m, hm⟩ := h.critDist_even
    have hb' : 2 < critDist (puAmalgam h.le) := by omega
    exact burnsideC134w_ms93ConclAS_of_endConcl h38 h45 h46 h512 h7 h hL hb'
      (hend G M T L h hb')

section C134

variable {G : Type} [Group G] [Finite G]

theorem burnsideC134w_corrBig_of_ms93ASBig_of_simple
    (hS : RankTwoLieSimple)
    (hNC5 : C134NotCentralizer5) (hNC11 : C134NotCentralizer11) (hNC13 : C134NotCentralizer13)
    (hms : burnsideC134w_MS93ASBig) : burnsideC134w_AS_C_1_34_corrBig := by
  intro G _ _ G₀ R L hMS hL hG hsl3
  obtain ⟨n, F, _, _, α, hn, hF, hα⟩ := hsl3
  have hbig : ¬ MRes.NotSL3Big L := fun hN => hN ⟨n, F, inferInstance, inferInstance, α, hn, hF, hα⟩
  have h := puHyp_of_msPair_of_simple hS hMS hL hG
  rcases hms G G₀ R L h hbig with
    h2 | h3 | h4 | ⟨hX5, h5⟩ | h6 | h8 | h10 | ⟨hX11, h11⟩ | ⟨hX13, h13⟩
  · exact (not_case2_of_sl3 h h2 hF hα).elim
  · exact (not_case3_of_sl3 h h3 hF hα).elim
  · exact ⟨1, isSL3Block_of_case4 h h4⟩
  · refine ⟨2, ?_, hNC5 G G₀ R L hMS hL hG h hX5 h5⟩
    obtain ⟨n', F', _, _, α', hF', hmod, hn'⟩ := isModO2Surj_of_case5 h h5
    exact ⟨n', F', inferInstance, inferInstance, α', hF', hmod, hn'⟩
  · exact (not_case6_of_sl3 h h6 hF hα).elim
  · exact ⟨5, isC134Case5_of_case8 hMS hL hG h h8⟩
  · exact (not_case10_of_sl3 h h10 hF hα).elim
  · refine ⟨3, ?_, hNC11 G G₀ R L hMS hL hG h hX11 h11⟩
    obtain ⟨n', F', _, _, α', hF', hα', h1, h2, -⟩ := h11
    exact ⟨n', F', inferInstance, inferInstance, α', hF',
      isModO2Surj_of_case11_data h hα' h1 h2, h1, h2⟩
  · refine ⟨4, ?_, hNC13 G G₀ R L hMS hL hG h hX13 h13⟩
    obtain ⟨n', F', _, _, α', hF', hα', hcard, hE, hZeq, hdisj, hU, hΦ, hC, hVC, -⟩ := h13
    exact ⟨n', F', inferInstance, inferInstance, α', hF',
      isModO2Surj_of_case13_data h hα' hZeq hU hΦ hC hVC, isE2_c134CQ_of_case13 hcard hE, hZeq,
      hdisj, hU, hΦ, hC, hVC⟩

end C134

section Holds

set_option linter.unusedSectionVars false


theorem burnsideC134w_ms93ASBig_holds
    (hsl : S4L.NoNonlinSLGt4) : burnsideC134w_MS93ASBig :=
  have h441 := s441_holds
  burnsideC134w_ms93ASBig_of s32_holds (s36_of_g2 s38G2_holds) s37_holds s18_holds
    (s38_of_g2 s38G2_holds)
    (burnsideC134w_s45Big_of s43_holds
      (s44_frontier h441 (S4A.s442_of_s441 ms14AS_holds sqtkQuot_holds s32_holds s43_holds h441))
      ms14AS_holds sqtkQuot_holds)
    (s46_frontier (S46R.s468Deg_of_degN s32_holds (s39_of s32_holds) (s42_of s32_holds) s43_holds
      ms14AS_holds sqtkQuot_holds
      (CFSG.Yardstones.M71b2fd3d34b9.burnsideD468_s468DegN_of_base s32_holds s43_holds ms14AS_holds
        sqtkQuot_holds)))
    s512_holds
    (s7two_of s32_holds (s36_of_g2 s38G2_holds) s18_holds)
    (S34D.end_of_endNL puReduce_holds
      (S34F.endNL_of_fDesc puReduce_holds
        (S4L.Core.fDesc_of_fDescN ms14AS_holds sqtkQuot_holds s32_holds
          (burnsideC134_s34FDescN hsl))))

theorem burnsideC134w_corrBig
    (hsl : S4L.NoNonlinSLGt4) : burnsideC134w_AS_C_1_34_corrBig :=
  burnsideC134w_corrBig_of_ms93ASBig_of_simple rankTwoLieSimple_holds c134NotCentralizer5_holds
    c134NotCentralizer11_holds c134NotCentralizer13_holds (burnsideC134w_ms93ASBig_holds hsl)

end Holds

end CFSG.Quasithin.MS93
