module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321Steps
public import CFSG.Quasithin.Vol2.Ch3Sec3Ln2D
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3322C
public import CFSG.Quasithin.EmptyFaithful.FLc3Ctx
public import CFSG.Quasithin.Background.FLc3Pos

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

namespace L3321

variable {G : Type} [Group G] [Finite G] {T M L D : Subgroup G}

theorem exists_normalized {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hS : IsSylowTwoOf (T ⊓ L) L) {n : ℕ} (hn : 3 ≤ n) (ρ₀ : FLc.SLt n →* MulAut ↥V)
    (hrange : ∀ k ∈ autOn L V, ∃ g, ρ₀ g = k) (hrange' : ∀ g, ρ₀ g ∈ autOn L V)
    (hne : ∃ g, ρ₀ g ≠ 1) :
    Function.Injective ρ₀ ∧ ∃ h : FLc.SLt n,
      Function.Injective (ρ₀.comp (MulAut.conj h).toMonoidHom) ∧
      (∀ k ∈ autOn L V, ∃ g, (ρ₀.comp (MulAut.conj h).toMonoidHom) g = k) ∧
      (∀ g, (ρ₀.comp (MulAut.conj h).toMonoidHom) g ∈ autOn L V) ∧
      ∀ u ∈ FLc.Ut n, (ρ₀.comp (MulAut.conj h).toMonoidHom) u ∈ autOn (T ⊓ L) V := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hV
  have := FLc.isSimpleGroup_SLt hn
  have hinj : Function.Injective ρ₀ := FLc.injective_of_ne_one ρ₀ hne
  have hsyl := FLc.exists_sylow_autOn hLV hS hrange hrange'
  have hTle : autOn (T ⊓ L) V ≤ ρ₀.range := fun a ha => by
    obtain ⟨x, hx, hxS, rfl⟩ := FLc.mem_autOn_iff.1 ha
    obtain ⟨g, hg⟩ := hrange _ (FLc.mem_autOn_iff.2 ⟨x, hx, hxS.2, rfl⟩)
    exact ⟨g, hg⟩
  have hn1 : 1 ≤ n := by omega
  obtain ⟨h, hh⟩ := FLc.exists_rho_conj hn1 hTle hsyl
  obtain ⟨hr1, hr2⟩ := rho_conj_range hrange hrange' h
  refine ⟨hinj, h, fun x y hxy => (MulAut.conj h).injective (hinj hxy), hr1, hr2, ?_⟩
  intro u hu
  rw [← hh]
  exact ⟨u, hu, rfl⟩

theorem mem_autOn_centralizer (h9 : Stmt3_3_9) (h : Hyp331 G T M L D) (hML : mPlus L T = L)
    {x : MulAut ↥(vPlus L T)} (hx : x ∈ autOn L (vPlus L T))
    (hfix : ∀ v : ↥(vPlus L T), (v : G) ∈ quasithinOmegaOneCenter T →
      (v : G) ∈ ⁅vPlus L T, L⁆ → x v = v) :
    x ∈ autOn (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) (vPlus L T) := by
  obtain ⟨l, hl, hlL, rfl⟩ := FLc.mem_autOn_iff.1 hx
  refine FLc.mem_autOn_iff.2 ⟨l, hl, ?_, rfl⟩
  have h9' := h9 G T M L D h
  rw [hML] at h9'
  have hlZ : l ∈ L ⊓ Subgroup.centralizer
      ((quasithinOmegaOneCenter T ⊓ ⁅vPlus L T, L⁆ : Subgroup G) : Set G) := by
    refine ⟨hlL, Subgroup.mem_centralizer_iff.2 fun z hz => ?_⟩
    have hzV : z ∈ vPlus L T := le_conjClosure _ _ hz.1
    have h1 := hfix ⟨z, hzV⟩ hz.1 hz.2
    have h2 := congrArg (fun w : ↥(vPlus L T) => (w : G)) h1
    simp only [FLc.conjAct_coe hl] at h2
    calc z * l = (l * z * l⁻¹) * l := by rw [h2]
      _ = l * z := by group
  rw [← h9'] at hlZ
  exact hlZ

abbrev rD (T L : Subgroup G) : Subgroup G :=
  pCoreOf 2 (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ⊔ T)

theorem setting_facts (h : Hyp331 G T M L D) (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    IsElemAbelian 2 (vPlus L T) ∧ L ≤ Subgroup.normalizer (vPlus L T : Set G) ∧
      T ≤ Subgroup.normalizer (vPlus L T : Set G) ∧ vPlus L T ≤ pCoreOf 2 (L ⊔ T) ∧
      pCoreOf 2 (L ⊔ T) ≤ rD T L ∧ rD T L ≤ T ∧
      (∀ m ∈ L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G), ∀ q ∈ rD T L,
        m * q * m⁻¹ ∈ rD T L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hVO, hVe, -⟩ := Hyp331.vPlus_reduced h.toSetup331
  have hLV := L3317.le_normalizer_vPlus h
  have hTV := Hyp331.le_normalizer_vPlus L T
  set C := L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) with hC
  have hTZ : T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    CFSG.QuasithinUnique.L246C127.le_centralizer_omegaOneCenter T
  have hTC : T ≤ Subgroup.normalizer (C : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ t ∈ T, ∀ x ∈ C, t * x * t⁻¹ ∈ C := by
      intro t ht x hx
      refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.mp (hTL ht) x).mp hx.1, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have h1 := Subgroup.mem_centralizer_iff.mp (hTZ ht) z hz
      have h2 := Subgroup.mem_centralizer_iff.mp hx.2 z hz
      have hz' : t⁻¹ * z * t = z := by
        calc t⁻¹ * z * t = t⁻¹ * (z * t) := by group
          _ = t⁻¹ * (t * z) := by rw [h1]
          _ = z := by group
      have hz'' : t * z * t⁻¹ = z := by
        calc t * z * t⁻¹ = (t * z) * t⁻¹ := rfl
          _ = (z * t) * t⁻¹ := by rw [h1]
          _ = z := by group
      calc z * (t * x * t⁻¹) = t * (t⁻¹ * z * t) * x * t⁻¹ := by group
        _ = t * (z * x) * t⁻¹ := by rw [hz']; group
        _ = t * (x * z) * t⁻¹ := by rw [h2]
        _ = t * x * t⁻¹ * (t * z * t⁻¹) := by group
        _ = t * x * t⁻¹ * z := by rw [hz'']
    intro x
    exact ⟨fun hx => key t ht x hx, fun hx => by
      have := key t⁻¹ (T.inv_mem ht) _ hx
      simpa [mul_assoc] using this⟩
  have hCTn : C ⊔ T ≤ Subgroup.normalizer (rD T L : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (C ⊔ T)
  have hTsyl : IsSylowTwoOf T (C ⊔ T) :=
    isSylowTwoOf_of_quasithinIsSylowTwo h.sylow le_sup_right
  have hRT : rD T L ≤ T := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hTsyl
  have hOR : pCoreOf 2 (L ⊔ T) ≤ rD T L := by
    have hOT : pCoreOf 2 (L ⊔ T) ≤ T :=
      EscapingLocal.pCoreOf_le_of_isSylowTwoOf h.toSetup331.isSylowTwoOf
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hOT.trans le_sup_right) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T))
    exact (sup_le_sup_right (inf_le_left : C ≤ L) T).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T))
  refine ⟨hVe, hLV, hTV, hVO.trans inf_le_left, hOR, hRT, fun m hm q hq => ?_⟩
  exact (Subgroup.mem_normalizer_iff.mp (hCTn (Subgroup.mem_sup_left hm)) q).mp hq

omit [Finite G] in
theorem fix_of_mem_autOn_inf {x : MulAut ↥(vPlus L T)} (hx : x ∈ autOn (T ⊓ L) (vPlus L T))
    {v : ↥(vPlus L T)} (hv : (v : G) ∈ quasithinOmegaOneCenter T) : x v = v := by
  obtain ⟨y, hy, hyS, rfl⟩ := FLc.mem_autOn_iff.1 hx
  apply Subtype.ext
  rw [FLc.conjAct_coe hy]
  have h1 := Subgroup.mem_centralizer_iff.mp
    (CFSG.QuasithinUnique.L246C127.le_centralizer_omegaOneCenter T hyS.1) (v : G) hv
  rw [← h1]
  group

omit [Finite G] in
theorem vPlus_le_conjClosure (hML : mPlus L T = L) :
    vPlus L T ≤ conjClosure (quasithinOmegaOneCenter T) L := by
  show conjClosure (quasithinOmegaOneCenter T) (mPlus L T) ≤ _
  rw [hML]

omit [Finite G] in
theorem conj_omegaOneCenter {s z : G} (hs : s ∈ T) (hz : z ∈ quasithinOmegaOneCenter T) :
    s * z * s⁻¹ = z := by
  have h1 := Subgroup.mem_centralizer_iff.mp
    (CFSG.QuasithinUnique.L246C127.le_centralizer_omegaOneCenter T hs) z hz
  rw [← h1]
  group

theorem no_offender_ext (h9 : Stmt3_3_9) (h : Hyp331 G T M L D) (hML : mPlus L T = L)
    (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hne : ∃ k ∈ autOn L (vPlus L T), k ≠ 1) [IsMulCommutative ↥(vPlus L T)]
    (hmod : Mod3321Ext T L) {A : Subgroup (MulAut ↥(vPlus L T))}
    (hAR : A ≤ autOn (rD T L) (vPlus L T)) (hA : A ≠ ⊥) :
    Nat.card A * Nat.card (fixV A) < Nat.card ↥(vPlus L T) := by
  obtain ⟨hVe, hLV, -, -, -, hRT, hCR⟩ := setting_facts h hTL
  obtain ⟨Z₀, hZ₀, -, hext⟩ := hmod
  have hV2 : ∀ w : ↥(vPlus L T), w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hVe.2 w w.2)
  obtain ⟨n, I, I', ρ₀, hn3, hrange', hrange, -, hII', hI', hasym, hfix, hmodn⟩ :=
    FLc.excl_ext4 hV2 (hZ₀.trans inf_le_left) hext
  have hS := L3317.isSylowTwoOf_inf h hTL
  obtain ⟨k, hk, hk1⟩ := hne
  obtain ⟨g₀, hg₀⟩ := hrange k hk
  obtain ⟨hρ₀inj, h', hinj, hr1, hr2, hT⟩ :=
    exists_normalized hVe hLV hS hn3 ρ₀ hrange hrange' ⟨g₀, by rw [hg₀]; exact hk1⟩
  have hQI : ∀ x ∈ FLc.QI n I, (ρ₀.comp (MulAut.conj h').toMonoidHom) x ∈
      autOn (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) (vPlus L T) := by
    intro x hx
    refine mem_autOn_centralizer h9 h hML (hr2 x) fun v hvZ hvW => ?_
    have hvc : v ∈ commV (autOn L (vPlus L T)) := by
      rw [Ln2.commV_autOn_eq h]
      exact hvW
    exact hfix h' v hvc (fun s hs => fix_of_mem_autOn_inf (hT s hs) hvZ) x hx
  exact FLc.core_not_ff_asym hVe hn3 _ hinj hLV (fun s hs l hl =>
      (Subgroup.mem_normalizer_iff.mp (hTL hs) l).mp hl) (vPlus_le_conjClosure hML)
    (le_conjClosure _ _) (fun s hs z hz => conj_omegaOneCenter hs hz) h.sylow.1 hRT hCR
    inf_le_left hr1 hr2 hT hII' hI' hasym hQI
    (fun A'' hU hR hne => hmodn hρ₀inj h' A'' hU hR hne) hAR hA

theorem no_offender_sum (h9 : Stmt3_3_9) (h : Hyp331 G T M L D) (hML : mPlus L T = L)
    (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hne : ∃ k ∈ autOn L (vPlus L T), k ≠ 1) [IsMulCommutative ↥(vPlus L T)]
    (hmod : Mod3321Sum T L) {A : Subgroup (MulAut ↥(vPlus L T))}
    (hAR : A ≤ autOn (rD T L) (vPlus L T)) (hA : A ≠ ⊥) :
    Nat.card A * Nat.card (fixV A) < Nat.card ↥(vPlus L T) := by
  obtain ⟨hVe, hLV, -, -, -, hRT, hCR⟩ := setting_facts h hTL
  obtain ⟨-, π, U₁, U₂, hdirect, hreal1, hreal2⟩ := hmod
  have hV2 : ∀ w : ↥(vPlus L T), w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hVe.2 w w.2)
  obtain ⟨D₁⟩ := FLc.vmodelNat hreal1
    (fun g _ z hz => by rw [Subgroup.mem_bot.1 hz]; exact map_one g)
  obtain ⟨D₂⟩ := FLc.vmodelDual hreal2
    (fun g _ z hz => by rw [Subgroup.mem_bot.1 hz]; exact map_one g)
  have hS := L3317.isSylowTwoOf_inf h hTL
  obtain ⟨k, hk, hk1⟩ := hne
  obtain ⟨g₀, hg₀⟩ := FLc.rhoOf_surj hreal1.1 k hk
  obtain ⟨-, h', hinj, hr1, hr2, hT⟩ := exists_normalized hVe hLV hS (by norm_num) (FLc.rhoOf π)
    (FLc.rhoOf_surj hreal1.1) (FLc.rhoOf_mem π) ⟨g₀, by rw [hg₀]; exact hk1⟩
  set ρ := (FLc.rhoOf π).comp (MulAut.conj h').toMonoidHom with hρ
  have D₁' := D₁.rtwist h'
  have D₂' := D₂.rtwist h'
  have hQ1 : FLc.QI 4 {1, 3} ≤ FLc.QI 4 {1} :=
    (FLc.QI_le_QI_iff (fun j hj => by
      rw [Set.mem_singleton_iff] at hj
      subst hj
      exact ⟨le_rfl, by omega⟩)).2 (by simp)
  have hQ3 : FLc.QI 4 {1, 3} ≤ FLc.QI 4 {3} :=
    (FLc.QI_le_QI_iff (fun j hj => by
      rw [Set.mem_singleton_iff] at hj
      subst hj
      exact ⟨by omega, by omega⟩)).2 (by simp)
  have hfixZ : ∀ x ∈ FLc.QI 4 {1, 3}, ∀ v : ↥(vPlus L T), (v : G) ∈ quasithinOmegaOneCenter T →
      (v : G) ∈ ⁅vPlus L T, L⁆ → ρ x v = v := by
    intro x hx v hvZ hvW
    have hvU : v ∈ U₁ ⊔ U₂ := by
      rw [hdirect.1, Ln2.commV_autOn_eq h]
      exact hvW
    obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Subgroup.mem_sup.1 hvU
    have hcomp : ∀ s ∈ FLc.Ut 4, ρ s v₁ = v₁ ∧ ρ s v₂ = v₂ := fun s hs =>
      FLc.fixed_of_two hdirect.2 (ρ s) (fun u hu => D₁'.inv s u hu) (fun u hu => D₂'.inv s u hu)
        hv₁ hv₂ (fix_of_mem_autOn_inf (hT s hs) hvZ)
    have h1 := FLc.fixQ_of_model D₁' hV2 (by norm_num) (c := 1)
      (fun a ha i hi hic => FLc.fix_nat a ha i hi hic) hv₁ (fun s hs => (hcomp s hs).1)
    have h2 := FLc.fixQ_of_model D₂' hV2 (by norm_num) (c := 3)
      (fun a ha i hi hic => FLc.fix_dual (by norm_num) a ha i hi (by omega)) hv₂
      (fun s hs => (hcomp s hs).2)
    rw [map_mul, h1 x (hQ1 hx), h2 x (hQ3 hx)]
  have hQJ : ∀ x ∈ FLc.QI 4 {1, 3}, ρ x ∈
      autOn (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) (vPlus L T) :=
    fun x hx => mem_autOn_centralizer h9 h hML (hr2 x) (hfixZ x hx)
  have hst := FLc.stSetting_ctx hVe ρ hinj hLV (fun s hs l hl =>
      (Subgroup.mem_normalizer_iff.mp (hTL hs) l).mp hl) (vPlus_le_conjClosure hML)
    (le_conjClosure _ _) (fun s hs z hz => conj_omegaOneCenter hs hz) h.sylow.1 hr1 hr2
    (fun u hu => FLc.autOn_mono' inf_le_left (hT u hu))
  have hnormQ := FLc.normQ_of_ctx ρ hLV hCR inf_le_left hQJ
  exact FLc.not_ff_sum_any (m := 2) (by norm_num) hst hV2 hdirect.2 D₁' D₂'
    (FLc.autOn_mono' hRT) hnormQ hAR hA

theorem no_offender (h9 : Stmt3_3_9) (h : Hyp331 G T M L D) (hML : mPlus L T = L)
    (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (e : ↥(autOn L (vPlus L T)) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
    (hmod : Mod3321 T L) (hVe : IsElemAbelian 2 (vPlus L T))
    {A : Subgroup (MulAut ↥(vPlus L T))} (hAR : A ≤ autOn (rD T L) (vPlus L T)) (hA : A ≠ ⊥) :
    Nat.card A * Nat.card (@fixV ↥(vPlus L T) (commGroupOfElemAbelian hVe) A) <
      Nat.card ↥(vPlus L T) := by
  have hcard : Nat.card ↥(autOn L (vPlus L T)) = 20160 := by
    rw [Nat.card_congr e.toEquiv, Ln2.card_specialLinear 4 (Or.inl rfl)]
    rfl
  have : Nontrivial ↥(autOn L (vPlus L T)) := Finite.one_lt_card_iff_nontrivial.1
    (by rw [hcard]; norm_num)
  obtain ⟨k, hk⟩ := exists_ne (1 : ↥(autOn L (vPlus L T)))
  have hne : ∃ k ∈ autOn L (vPlus L T), k ≠ 1 :=
    ⟨k, k.2, fun h1 => hk (Subtype.ext h1)⟩
  obtain ⟨hc, hm | hm⟩ := hmod
  · exact no_offender_ext h9 h hML hTL hne hm hAR hA
  · exact no_offender_sum h9 h hML hTL hne hm hAR hA

theorem le_centralizer_of_isMaxElemAbelian (h9 : Stmt3_3_9) (h : Hyp331 G T M L D)
    (hML : mPlus L T = L) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (e : ↥(autOn L (vPlus L T)) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
    (hmod : Mod3321 T L) {A : Subgroup G} (hA : IsMaxElemAbelian (rD T L) A) :
    A ≤ Subgroup.centralizer (vPlus L T : Set G) := by
  obtain ⟨hVe, -, hTV, hVO, hOR, hRT, -⟩ := setting_facts h hTL
  have hRN : rD T L ≤ Subgroup.normalizer (vPlus L T : Set G) := hRT.trans hTV
  have hAN : A ≤ Subgroup.normalizer (vPlus L T : Set G) := hA.1.trans hRN
  by_contra hAc
  have hAs : autI hVe A ≠ ⊥ := by
    intro hbot
    apply hAc
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h1 : convI hVe ⟨a, hAN ha⟩ = 1 := by
      have h2 : convI hVe ⟨a, hAN ha⟩ ∈ autI hVe A := convI_mem_autI hVe ha (hAN ha)
      rw [hbot] at h2
      exact Subgroup.mem_bot.1 h2
    have h3 := convI_apply_val hVe ⟨a, hAN ha⟩ (IntMod.mk hVe ⟨v, hv⟩)
    rw [h1] at h3
    have h4 : v = a * v * a⁻¹ := h3
    calc v * a = (a * v * a⁻¹) * a := by rw [← h4]
      _ = a * v := by group
  have hlt := no_offender h9 h hML hTL e hmod hVe (A := autOn A (vPlus L T))
    (FLc.autOn_mono' hA.1) hAs
  have hcore := (offender_core hVe (hVO.trans hOR) hRN hA
    (bot_le : (⊥ : Subgroup (MulAut (IntMod (vPlus L T) hVe))) ≤ autI hVe A)).1
  rw [Subgroup.card_bot, B1.fixV_bot, Subgroup.card_top, one_mul] at hcore
  exact absurd hlt (not_lt.2 hcore)

theorem step3_3_21d_of (h5 : Stmt3_3_5) (h7 : Stmt3_3_7) (h9 : Stmt3_3_9) (h14 : Stmt3_3_14) :
    Step3_3_21d := by
  intro G _ _ T M L D h ⟨e⟩ hmod
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hML, hMN⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hMN
  obtain ⟨hVe, -, -, hVO, hOR, hRT, -⟩ := setting_facts h hTL
  have hJC : thompsonJ (rD T L) ≤ Subgroup.centralizer (vPlus L T : Set G) :=
    iSup₂_le fun A hA => le_centralizer_of_isMaxElemAbelian h9 h hML hTL e hmod hA
  have h7' := (h7 G T M L D h).1.2
  rw [hML] at h7'
  have hJO : thompsonJ (rD T L) ≤ pCoreOf 2 (L ⊔ T) := by
    rw [← h7']
    exact le_inf ((thompsonJ_le_self _).trans hRT) hJC
  have hJeq : thompsonJ (rD T L) = thompsonJ (pCoreOf 2 (L ⊔ T)) := thompsonJ_eq_of_le hJO hOR
  intro g hg
  have hgJ : g ∈ Subgroup.normalizer (thompsonJ (rD T L) : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.2 (cjSub_thompsonJ hg)
  rw [hJeq] at hgJ
  refine L3322.normalizer_le_M h5 h hML ?_ ?_ ?_ hgJ
  ·
    obtain ⟨A, hA⟩ := exists_isMaxElemAbelian (pCoreOf 2 (L ⊔ T))
    have hAJ : A ≤ thompsonJ (pCoreOf 2 (L ⊔ T)) := le_iSup₂_of_le A hA le_rfl
    intro hbot
    rw [hbot, le_bot_iff] at hAJ
    have hVA := hA.2.2 (vPlus L T) hVO hVe
    rw [hAJ, Subgroup.card_bot] at hVA
    have hsubV : Subsingleton ↥(vPlus L T) := Finite.card_le_one_iff_subsingleton.1 hVA
    have hsub : Subsingleton (MulAut ↥(vPlus L T)) :=
      ⟨fun a b => MulEquiv.ext fun v => Subsingleton.elim _ _⟩
    have h1 : Nat.card ↥(autOn L (vPlus L T)) ≤ 1 := by
      have : Subsingleton ↥(autOn L (vPlus L T)) :=
        ⟨fun a b => Subtype.ext (Subsingleton.elim (a : MulAut ↥(vPlus L T)) b)⟩
      exact Finite.card_le_one_iff_subsingleton.2 this
    rw [Nat.card_congr e.toEquiv, Ln2.card_specialLinear 4 (Or.inl rfl)] at h1
    norm_num at h1
  · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T)).to_le (thompsonJ_le_self _)
  · intro x hx
    exact Subgroup.mem_normalizer_iff_map_conj_eq.2
      (cjSub_thompsonJ (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T) hx))

end L3321

end CFSG.Quasithin.H13
