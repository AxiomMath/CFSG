module

public import CFSG.Quasithin.MS93.ASC134Sq
public import CFSG.Quasithin.MS93.MResOrd
public import CFSG.Quasithin.MS93.Burnside.MS93RRed
public import CFSG.Quasithin.EmptyFaithful.SzMSWAsm
public import CFSG.Quasithin.EmptyFaithful.SzMSWFin
public import CFSG.Quasithin.MS93.ASC134C5
public import CFSG.Quasithin.MS93.ASC134NC5
public import CFSG.Quasithin.MS93.MRes46
public import CFSG.Quasithin.MS93.MResC13

public section

namespace CFSG.Quasithin.MS93.MRes

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S45
open scoped Pointwise commutatorElement Matrix

theorem card_zq_le_of_sq {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type}
    [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx M T L φ)
    (hsq : Nat.card ↥(omegaOneCenterOf T ⊓ Subgroup.centralizer (L : Set G)) ^ 2 ≤
      Nat.card ↥(omegaOneCenterOf T)) :
    Nat.card ↥(Zq M L) ≤ Fintype.card F ^ 2 := by
  have h := c.hyp
  have hfull : IsSL3Full M T L := c.full
  obtain ⟨-, hZM, hXZ, -⟩ := s41_holds G M T L h hfull
  have hAZ : omegaOneCenterOf T ⊓ Subgroup.centralizer (L : Set G) = Zq M L := by
    rw [h.omegaOneCenterOf_eq]
    refine le_antisymm ?_ ?_
    · rintro x ⟨⟨hxX, -⟩, hxL⟩
      exact ⟨hxX, hxL⟩
    · rintro x ⟨hxX, hxL⟩
      exact ⟨⟨hxX, Subgroup.centralizer_le h.le (hZM ⟨hxX, hxL⟩)⟩, hxL⟩
  have hsq' : Nat.card ↥(Zq M L) ^ 2 ≤ Nat.card ↥(omegaOneCenterOf T) := by
    rwa [hAZ] at hsq
  have hZU : Zq M L ⊓ Uq M T L = ⊥ := c.via.2.2.2.1
  have hX : Xq M = Zq M L ⊔ Uq M T L := c.via.2.2.1
  have hUX : Uq M T L ≤ Xq M := le_sup_right.trans hX.symm.le
  have hcomm : Uq M T L ≤ Subgroup.centralizer (Zq M L : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact isMulCommutative_subgroup_iff.mp h.isElemAbelian_Xq.1 z hz.1 u (hUX hu)
  have hcardU : Nat.card ↥(Uq M T L) = Fintype.card F ^ 3 := by
    rw [card_eq_of_natural c.via.2.2.2.2, Nat.card_eq_fintype_card]
  have hcardX : Nat.card ↥(Xq M) = Nat.card ↥(Zq M L) * Fintype.card F ^ 3 := by
    rw [hX, card_sup_of_commute hcomm hZU, hcardU]
  have hcardZ0 : Nat.card ↥(Z0q M T) = Nat.card ↥(Zq M L) * Fintype.card F ^ 3 := by
    rw [← hXZ, hcardX]
  have hab := adj_baseA_baseB (puAmalgam h.le)
  have hbase := isMVtx_baseA (puAmalgam h.le)
  have hU : (Uq M T L ⊓ Subgroup.centralizer (T : Set G)).relIndex (Uq M T L) =
      Fintype.card F := by
    have := c.relIndex_zh hbase hab
    rwa [puAmalgam.zh_baseB, puAmalgam.zm_baseA, S46.relIndex_imM h.le (normalClosureIn_le _ _),
      ← S46.relIndex_Uq_inf_centralizer h c.via] at this
  have hrelA : (omegaOneCenterOf T).relIndex (Z0q M T) = Fintype.card F := by
    rw [← S46.relIndex_Uq_inf_centralizer h c.via]
    exact hU
  have hcardA : Nat.card ↥(Z0q M T) = Fintype.card F * Nat.card ↥(omegaOneCenterOf T) := by
    have := Subgroup.relIndex_mul_card (omegaOneCenterOf T) (Z0q M T)
    rw [hrelA, inf_of_le_left (le_normalClosureIn ((PU.omegaOneCenterOf_le T).trans h.le))] at this
    exact this.symm
  have hAeq : Nat.card ↥(omegaOneCenterOf T) =
      Fintype.card F ^ 2 * Nat.card ↥(Zq M L) := by
    have hqpos : 0 < Fintype.card F := Fintype.card_pos
    refine Nat.eq_of_mul_eq_mul_left hqpos ?_
    calc Fintype.card F * Nat.card ↥(omegaOneCenterOf T)
        = Nat.card ↥(Z0q M T) := hcardA.symm
      _ = Nat.card ↥(Zq M L) * Fintype.card F ^ 3 := hcardZ0
      _ = Fintype.card F * (Fintype.card F ^ 2 * Nat.card ↥(Zq M L)) := by ring
  have hmain : Nat.card ↥(Zq M L) * Nat.card ↥(Zq M L) ≤
      Fintype.card F ^ 2 * Nat.card ↥(Zq M L) := by
    rw [hAeq] at hsq'
    simpa [pow_two] using hsq'
  exact Nat.le_of_mul_le_mul_right hmain Nat.card_pos

private theorem card_zloc {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
    (h : PUHyp M T L) {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) :
    Nat.card ↥(Zloc h.le L δ) = Nat.card ↥(Zq M L) := by
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hδ
  rw [zloc_smul h, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hbase : Zloc h.le L (baseA (puAmalgam h.le)) = imM h.le (Zq M L) :=
    puTrans_baseA h.le (S4A.Zq_normal h)
  rw [hbase, S45.card_imM h.le Zq_le]

theorem zloc_le_hloc_of_card_zq {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
    {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx M T L φ)
    (hZq : Nat.card ↥(Zq M L) ≤ Fintype.card F ^ 2)
    {p : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ} (hp : IsGoodPath _ p N) {a : ℕ}
    (ha : Even a) (h34 : 34 ≤ a) (haN : a + 30 ≤ N) :
    Zloc c.hyp.le L (p a) ≤ Hloc c.hyp.le L (p a) := by
  have h := c.hyp
  have hM : IsMVtx (puAmalgam h.le) (p a) :=
    c.isMVtx_of_isGoodPath hp (k := a) (by omega) ha
  have ha6 : Even (a - 6) := (Nat.even_sub (by omega)).mpr (iff_of_true ha (by decide))
  have hHc := c.card_hloc hp (x := a - 6) ha6 (by omega) (by omega)
  rw [show a - 6 + 6 = a by omega] at hHc
  have hZc : Nat.card ↥(Zloc h.le L (p a)) = Nat.card ↥(Zq M L) := card_zloc h hM
  have hHZ : Hloc h.le L (p a) ≤ Zloc h.le L (p a) :=
    (Subgroup.commutator_mono (c.vcirc_le_vv _) le_rfl).trans (c.commutator_vv_qv_le_zloc hM)
  have hcard : Nat.card ↥(Zloc h.le L (p a)) ≤ Nat.card ↥(Hloc h.le L (p a)) := by
    rw [hHc, hZc]
    exact hZq
  haveI hfinZ : Finite ↥(Zloc h.le L (p a)) :=
    Nat.finite_of_card_ne_zero (by rw [hZc]; exact Nat.card_pos.ne')
  haveI hfinH : Finite ↥(Hloc h.le L (p a)) :=
    Nat.finite_of_card_ne_zero (by rw [hHc]; exact pow_ne_zero 2 (Fintype.card_pos.ne'))
  exact (Subgroup.eq_of_le_of_card_ge hHZ hcard).ge

theorem hQ2b_of_card_zq {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type}
    [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (h14 : MS14AS) (hSQ : SQTKQuot)
    (c : Ctx M T L φ) (hZV : c.HZV)
    (hZq : Nat.card ↥(Zq M L) ≤ Fintype.card F ^ 2) : c.HQ2b := by
  intro p p' N hp hp' a ha h34 haN hpp' hU1 hU3
  have hQ4 := S45Q4.hQ4 c
  have hC1 : ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ ⊓ Zloc c.hyp.le L (p a) ≤
      Hloc c.hyp.le L (p a) :=
    inf_le_right.trans (zloc_le_hloc_of_card_zq c hZq hp ha h34 haN)
  have hC4 := S45R.Ctx.not_frattiniIn_le c h14 hSQ hZV hp ha h34 haN
  exact ⟨c.inf_centralizer_ltil_le h14 hSQ hZV hQ4 hp hp' ha h34 haN hpp' hU1 hU3 hC1,
    c.center_le_uloc_sup_hloc h14 hSQ hZV hQ4 hp hp' ha h34 haN hpp' hU1 hU3 hC1,
    c.frattiniIn_eq_vcirc h14 hSQ hZV hQ4 hp hp' ha h34 haN hpp' hU1 hU3 hC1 hC4,
    c.inf_centralizer_vcirc_le_whv h14 hSQ hZV hQ4 hp hp' ha h34 haN hpp' hU1 hU3,
    c.commutator_qv_ltil_le_top hZV hp hp' ha h34 haN hpp' hU3⟩

theorem case13_of_sq {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
    (h43 : S43) (h44 : S44) (h14 : MS14AS) (hSQ : SQTKQuot) (hQ2a : S45Q2a)
    (h : PUHyp M T L) (hmin : PUMin M T L) (hb : 4 < critDist (puAmalgam h.le))
    (hfull : IsSL3Full M T L) (hL : NotSL3Big L)
    (hsq : Nat.card ↥(omegaOneCenterOf T ⊓ Subgroup.centralizer (L : Set G)) ^ 2 ≤
      Nat.card ↥(omegaOneCenterOf T)) :
    MS93Case13 (Vq M L) T L := by
  obtain ⟨F, _, _, φ, hφ⟩ := isSL3Full_iff_exists_via.mp hfull
  have hq := card_eq_two_of_via h hL hφ
  have c : Ctx M T L φ := Ctx.ofItems h43 h44 h hmin hb hφ
  have hZV : c.HZV := hQ2a G M T L F φ c hq
  obtain ⟨p, hp⟩ := c.exists_isGoodPath_of_ctx 28
  have hα := c.isMVtx_of_isGoodPath hp (k := 34) (by omega) (by decide)
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isMVtx _ hα (isMVtx_baseA _)
  have hZq : Nat.card ↥(Zq M L) ≤ Fintype.card F ^ 2 := card_zq_le_of_sq c hsq
  obtain ⟨ψ₀, hψ₀, hU₀, hHc, hF4, hF3, hZL, h₁, h₂, h₃⟩ :=
    c.exists_case13_of_isGoodPath h14 hSQ hZV (hQ2b_of_card_zq h14 hSQ c hZV hZq)
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

theorem ms93ConclASW_of_sq {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
    (h32 : S32) (h36 : S36) (h37 : S37) (h18 : S18) (h38 : S38) (h43 : S43) (h44 : S44)
    (h14 : MS14AS) (hSQ : SQTKQuot) (hQ2a : S45Q2a) (h45W : SzMSW.S45W) (h46 : S46Two)
    (h512 : S512) (h7 : S7Two) (h : PUHyp M T L) (hL : NotSL3Big L) (hS : NoSp4Quot L)
    (hsq : C134SqCond T L) : SzMSW.MS93ConclASW M T L := by
  by_cases hb : critDist (puAmalgam h.le) = 2
  · exact SzMSW.ms93ConclASW_of_critDist_eq_two h32 h36 h37 h18 h hb
  have hpos := h.critDist_pos
  obtain ⟨m, hm⟩ := h.critDist_even
  have hb' : 2 < critDist (puAmalgam h.le) := by omega
  obtain ⟨T₁, hT₁, hchar, -, h₁, hmin₁, hV₁⟩ := burnsideMS93R_exists_charMin h
  have hpos₁ := h₁.critDist_pos
  obtain ⟨m₁, hm₁⟩ := h₁.critDist_even
  by_cases hb₁ : critDist (puAmalgam h₁.le) = 2
  · have h5 := h7 G M T L (L ⊔ T₁) T₁ h h₁ hT₁ hmin₁ hV₁ hb' hb₁
    have hX : Xq M ≤ Zq M L ⊔ Uq M T L := by
      rcases h38 G M T L h hb' with hSL | hSp
      · exact hSL.1.le
      · exact (case5_sp4U_false h h5 hSp).elim
    exact SzMSW.MS93ConclASW.of_case5 hX h5
  have hb₁' : 2 < critDist (puAmalgam h₁.le) := by omega
  have hgood : (IsSL3U (L ⊔ T₁) T₁ L → IsSL3Full (L ⊔ T₁) T₁ L) ∧
      (IsSp4U (L ⊔ T₁) T₁ L → IsSp4Full (L ⊔ T₁) T₁ L) :=
    ⟨isSL3Full_of_isSL3U h₁ hL, isSp4Full_of_isSp4U_of_noSp4 h₁ hS⟩
  rcases h38 G (L ⊔ T₁) T₁ L h₁ hb₁' with hSL₁ | hSp₁
  swap
  · exact (h512 G (L ⊔ T₁) T₁ L h₁ hmin₁ hb₁' (hgood.2 hSp₁)).elim
  have hX : Xq M ≤ Zq M L ⊔ Uq M T L := by
    rcases h38 G M T L h hb' with hSL | hSp
    · exact hSL.1.le
    · exact (sl3U_sp4U_false h h₁ hSL₁ hSp).elim
  have hFull := hgood.1 hSL₁
  rcases (show critDist (puAmalgam h₁.le) = 4 ∨ 4 < critDist (puAmalgam h₁.le) by omega)
    with h4 | h4
  · have h11 := h46 G (L ⊔ T₁) T₁ L h₁ hmin₁ h4 hFull hL
    rw [hV₁] at h11
    exact SzMSW.MS93ConclASW.of_case11 hX (h11.mono hT₁)
  · have h13 := case13_of_sq h43 h44 h14 hSQ hQ2a h₁ hmin₁ h4 hFull hL (hsq T₁ hT₁ hchar)
    have hW := h45W G (L ⊔ T₁) T₁ L h₁ hmin₁ h4 hFull
    rw [hV₁] at h13 hW
    exact SzMSW.MS93ConclASW.of_case13 hX (h13.mono hT₁) hW

theorem isC134CaseCorrW_of_ms93ConclASW
    {G : Type} [Group G] [Finite G]
    {G₀ R L : Subgroup G} (hNC5 : C134NotCentralizer5) (hNC11 : C134NotCentralizer11)
    (hNC13 : C134NotCentralizer13) (hMS : IsMSPair G₀ R) (hL : L ∈ cComp G₀)
    (hG : (G₀ : Set G) = (L : Set G) * (R : Set G)) {F : Type} [Field F] [Fintype F]
    {α : ↥L →* ↥(StatedSL 3 F)} (hF2 : Fintype.card F = 2) (hα : IsModO2Surj L α)
    (h : PUHyp G₀ R L) (hc : SzMSW.MS93ConclASW G₀ R L) :
    ∃ i : ℕ, SzMSW.IsC134CaseCorrW i G₀ R L := by
  have hF : Fintype.card F = 2 ^ 1 := by rw [hF2, pow_one]
  rcases hc with h2 | h3 | h4 | ⟨hX5, h5⟩ | h6 | h8 | h10 | ⟨hX11, h11⟩ | ⟨hX13, h13, hW⟩
  · exact (not_case2_of_sl3 h h2 hF hα).elim
  · exact (not_case3_of_sl3 h h3 hF hα).elim
  · exact ⟨1, isSL3Block_of_case4 h h4⟩
  · refine ⟨2, ?_, hNC5 G G₀ R L hMS hL hG h hX5 h5⟩
    obtain ⟨n', F', _, _, α', hF', hmod, hn⟩ := isModO2Surj_of_case5 h h5
    exact ⟨n', F', inferInstance, inferInstance, α', hF', hmod, hn⟩
  · exact (not_case6_of_sl3 h h6 hF hα).elim
  · exact ⟨5, isC134Case5_of_case8 hMS hL hG h h8⟩
  · exact (not_case10_of_sl3 h h10 hF hα).elim
  · refine ⟨3, ?_, hNC11 G G₀ R L hMS hL hG h hX11 h11⟩
    obtain ⟨n', F', _, _, α', hF', hα', h1, h2, -⟩ := h11
    exact ⟨n', F', inferInstance, inferInstance, α', hF',
      isModO2Surj_of_case11_data h hα' h1 h2, h1, h2⟩
  · refine ⟨4, ⟨?_, hNC13 G G₀ R L hMS hL hG h hX13 h13⟩, hW⟩
    obtain ⟨n', F', _, _, α', hF', hα', hcard, hE, hZeq, hdisj, hU, hΦ, hC, hVC, -⟩ := h13
    exact ⟨n', F', inferInstance, inferInstance, α', hF',
      isModO2Surj_of_case13_data h hα' hZeq hU hΦ hC hVC, isE2_c134CQ_of_case13 hcard hE, hZeq,
      hdisj, hU, hΦ, hC, hVC⟩

section Holds


theorem asC134_corrWOneSq_holds
    : AS_C_1_34_corrWOneSq := by
  intro G _ _ G₀ R L hMS hL hG hsl3 hsq
  obtain ⟨F, _, _, α, hF2, hα⟩ := hsl3
  have h := puHyp_of_msPair_of_simple rankTwoLieSimple_holds hMS hL hG
  have h441 := s441_holds
  have h44 :=
    s44_frontier h441 (S4A.s442_of_s441 ms14AS_holds sqtkQuot_holds s32_holds s43_holds h441)
  have hc := ms93ConclASW_of_sq s32_holds (s36_of_g2 s38G2_holds) s37_holds s18_holds
    (s38_of_g2 s38G2_holds) s43_holds h44 ms14AS_holds sqtkQuot_holds S45J.s45Q2a_holds
    (SzMSW.s45W_of s43_holds h44 ms14AS_holds sqtkQuot_holds S45J.s45Q2a_holds)
    (s46Two_of s32_holds (s39_of s32_holds) (s42_of s32_holds) s43_holds ms14AS_holds
      sqtkQuot_holds)
    s512_holds (s7two_of s32_holds (s36_of_g2 s38G2_holds) s18_holds) h
    (notSL3Big_of_isModO2Surj_two hF2 hα) (noSp4Quot_of_isModO2Surj_two hF2 hα) hsq
  exact isC134CaseCorrW_of_ms93ConclASW c134NotCentralizer5_holds c134NotCentralizer11_holds
    c134NotCentralizer13_holds hMS hL hG hF2 hα h hc

theorem asC134_corrOneSq_holds
    : AS_C_1_34_corrOneSq :=
  corrOneSq_of_corrWOneSq asC134_corrWOneSq_holds

end Holds

end CFSG.Quasithin.MS93.MRes
