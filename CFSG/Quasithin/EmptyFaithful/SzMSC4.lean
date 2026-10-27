module

public import CFSG.Quasithin.MS93.C134L32CorrMOne
public import CFSG.Quasithin.EmptyFaithful.S151S9B
public import CFSG.Quasithin.EmptyFaithful.S151S9PW
public import CFSG.Quasithin.EmptyFaithful.S151S9A
public import CFSG.Quasithin.EmptyFaithful.S151S9P1
public import CFSG.Quasithin.EmptyFaithful.S151S9P3
public import CFSG.Quasithin.EmptyFaithful.S151S9P4
public import CFSG.Quasithin.EmptyFaithful.S151ZH

public section

namespace CFSG.Quasithin

namespace HSRuLoc

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint
open scoped Pointwise

variable {G : Type} [Group G]

theorem c134Ex_case4_min [Finite G] {K Q Z A₃ A₄ T : Subgroup G} {e n : ℕ} {F : Type}
    [Field F] [Fintype F] (hF : Fintype.card F = 2 ^ n)
    {α : ↥K →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)} (hTZ : T ≤ Z)
    (h1 : IsSumOfNaturalModulesVia K A₃ Z α true 1)
    (h2 : IsSumOfNaturalModulesVia K A₄ A₃ α true 2)
    (h3 : IsSumOfNaturalModulesVia K Q A₄ α false 2)
    (he : e < 13) (hcard : Nat.card ↥Q = 2 ^ e * Nat.card ↥T) : False := by
  have h1c := c134Ex_card_of_sum h1
  have h2c := c134Ex_card_of_sum h2
  have h3c := c134Ex_card_of_sum h3
  have hq : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  have h3' : Nat.card (Fin 3) = 3 := by simp
  rw [h3', hq] at h1c h2c h3c
  have hpow : (2 ^ n) ^ (3 * 1) * (2 ^ n) ^ (3 * 2) * (2 ^ n) ^ (3 * 2) = (2 ^ n) ^ 15 := by
    rw [← pow_add, ← pow_add]
  have hQ : Nat.card ↥Q = Nat.card ↥Z * 2 ^ (15 * n) := by
    calc Nat.card ↥Q = Nat.card ↥A₄ * (2 ^ n) ^ (3 * 2) := h3c
      _ = (Nat.card ↥A₃ * (2 ^ n) ^ (3 * 2)) * (2 ^ n) ^ (3 * 2) := by rw [h2c]
      _ = ((Nat.card ↥Z * (2 ^ n) ^ (3 * 1)) * (2 ^ n) ^ (3 * 2)) * (2 ^ n) ^ (3 * 2) := by rw [h1c]
      _ = Nat.card ↥Z * ((2 ^ n) ^ (3 * 1) * (2 ^ n) ^ (3 * 2) * (2 ^ n) ^ (3 * 2)) := by ring
      _ = Nat.card ↥Z * (2 ^ n) ^ 15 := by rw [hpow]
      _ = Nat.card ↥Z * 2 ^ (15 * n) := by
          rw [← pow_mul, Nat.mul_comm n 15]
  have hQle : Nat.card ↥Q ≤ 2 ^ e * Nat.card ↥Z := by
    rw [hcard]
    exact Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hTZ)
  have hstep : 2 ^ (15 * n) ≤ 2 ^ e := by
    have h := hQle
    rw [hQ] at h
    rw [mul_comm (2 ^ e) (Nat.card ↥Z)] at h
    exact Nat.le_of_mul_le_mul_left h Nat.card_pos
  have hn : 1 ≤ n := (c134Ex_card_field hF).1
  have h15 : 15 * n ≤ e := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hstep
  omega

theorem not_c134_of_exclHyp_corrM [Finite G] {K S : Subgroup G} {e : ℕ} (h : ExclHyp K S e) :
    ∀ i : ℕ, ¬ IsC134CaseM i (K ⊔ S) S K := by
  obtain ⟨⟨x, hxQ, hx2⟩, ⟨T, hTC, hTZ, hTcard⟩, he5, he13, he9⟩ := h
  have hTK : ∀ t ∈ T, ∀ a ∈ K, a * t = t * a := fun t ht a ha =>
    Subgroup.mem_centralizer_iff.1 (hTC ht).2 a ha
  intro i hi
  rcases i with _ | _ | _ | _ | _ | _ | i
  · exact hi
  · obtain ⟨_, n, F, _, _, hF, _, _, _, _, β, _, hβk, _⟩ := hi
    exact c134Ex_case12 hF β hβk hxQ hx2
  · obtain ⟨⟨n, F, _, _, α, hF, _, _, _, β, _, hβk, _⟩, _⟩ := hi
    exact c134Ex_case12 hF β hβk hxQ hx2
  · obtain ⟨⟨n, F, _, _, α, hF, ⟨hα, _⟩, h1, h2⟩, _⟩ := hi
    exact he9 (c134Ex_case3 hF hα hTK hTZ h1 h2 hTcard)
  · obtain ⟨⟨n, F, _, _, α, hF, _, _, _, _, ⟨A₃, A₄, h1, h2, h3⟩, -⟩, _⟩ := hi
    exact c134Ex_case4_min hF hTZ h1 h2 h3 he13 hTcard
  · obtain ⟨⟨α, _, hCQ, h1⟩, _⟩ := hi
    exact c134Ex_case5 hCQ h1 he5 hTcard
  · exact hi

theorem not_c134_of_exclHyp_corr [Finite G] {K S : Subgroup G} {e : ℕ} (h : ExclHyp K S e) :
    ∀ i : ℕ, ¬ MS93.IsC134CaseCorr i (K ⊔ S) S K := by
  intro i hi
  exact not_c134_of_exclHyp_corrM h i hi.toCaseM

end HSRuLoc

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Timmesfeld.Orders
  CFSG.Quasithin.H13.VolI CFSG.Quasithin.Vol2.Ch10.SecA CFSG.LieType.BorelTits
open scoped Pointwise

@[expose] def Input15122HSRuLocalCorr : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L S : Subgroup G), CFSG.Open.IsQuasisimple ↥L →
    IsPGroup 2 ↥(Subgroup.center ↥L) →
    (IsSporadic .HS (↥L ⧸ CFSG.pCore 2 ↥L) ∨ IsSporadic .Ru (↥L ⧸ CFSG.pCore 2 ↥L)) →
    IsPGroup 2 ↥S → S ≤ Subgroup.normalizer (L : Set G) → IsSylowTwoOf (S ⊓ L) L →
    ¬ L ≤ Subgroup.centralizer (centerOf (S ⊓ L) : Set G) →
    ∃ K : Subgroup G, K ≤ L ∧ S ≤ Subgroup.normalizer (K : Set G) ∧ K ∈ cComp (K ⊔ S) ∧
      IsSylowTwoOf S (K ⊔ S) ∧ CharTwo K ∧
      (∃ α : ↥K →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)), IsModO2Surj K α) ∧
      ¬ K ≤ Subgroup.centralizer (centerOf (S ⊓ L) : Set G) ∧
      ∀ i : ℕ, ¬ MS93.IsC134CaseCorr i (K ⊔ S) S K

@[expose] def Input15122HSRuLocalCorrM : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L S : Subgroup G), CFSG.Open.IsQuasisimple ↥L →
    IsPGroup 2 ↥(Subgroup.center ↥L) →
    (IsSporadic .HS (↥L ⧸ CFSG.pCore 2 ↥L) ∨ IsSporadic .Ru (↥L ⧸ CFSG.pCore 2 ↥L)) →
    IsPGroup 2 ↥S → S ≤ Subgroup.normalizer (L : Set G) → IsSylowTwoOf (S ⊓ L) L →
    ¬ L ≤ Subgroup.centralizer (centerOf (S ⊓ L) : Set G) →
    ∃ K : Subgroup G, K ≤ L ∧ S ≤ Subgroup.normalizer (K : Set G) ∧ K ∈ cComp (K ⊔ S) ∧
      IsSylowTwoOf S (K ⊔ S) ∧ CharTwo K ∧
      (∃ α : ↥K →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)), IsModO2Surj K α) ∧
      ¬ K ≤ Subgroup.centralizer (centerOf (S ⊓ L) : Set G) ∧
      ∀ i : ℕ, ¬ IsC134CaseM i (K ⊔ S) S K

open HSRuLoc in
theorem input15122HSRuLocalCorr_of_models (hHS : Input15122HSModel) (hRu : Input15122RuModel) :
    Input15122HSRuLocalCorr := by
  intro G _ _ L S hLq hZ hHR hS2 hSN hsyl hnc
  have hnorm : (CFSG.pCore 2 ↥L).Normal := inferInstance
  let π : ↥L →* (↥L ⧸ CFSG.pCore 2 ↥L) := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = CFSG.pCore 2 ↥L := QuotientGroup.ker_mk' _
  have hmod : HSRuModelFor (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rcases hHR with h | h
    · exact hHS _ h
    · exact hRu _ h
  obtain ⟨K, R, e, hm⟩ := hmod _ (isSylowTwoOf_map L S π hπ hker hsyl)
  have c : LiftCtx L S π _ K R e := ⟨hLq, hZ, hπ, hker, hS2, hSN, hsyl, hnc, rfl, hm⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := lift_struct c
  have hx := lift_excl c
  exact ⟨liftK L π K, h1, h2, h3, h4, h5, h6, h7, not_c134_of_exclHyp_corr hx⟩

open HSRuLoc in
theorem input15122HSRuLocalCorrM_of_models (hHS : Input15122HSModel) (hRu : Input15122RuModel) :
    Input15122HSRuLocalCorrM := by
  intro G _ _ L S hLq hZ hHR hS2 hSN hsyl hnc
  have hnorm : (CFSG.pCore 2 ↥L).Normal := inferInstance
  let π : ↥L →* (↥L ⧸ CFSG.pCore 2 ↥L) := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = CFSG.pCore 2 ↥L := QuotientGroup.ker_mk' _
  have hmod : HSRuModelFor (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rcases hHR with h | h
    · exact hHS _ h
    · exact hRu _ h
  obtain ⟨K, R, e, hm⟩ := hmod _ (isSylowTwoOf_map L S π hπ hker hsyl)
  have c : LiftCtx L S π _ K R e := ⟨hLq, hZ, hπ, hker, hS2, hSN, hsyl, hnc, rfl, hm⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := lift_struct c
  have hx := lift_excl c
  exact ⟨liftK L π K, h1, h2, h3, h4, h5, h6, h7, not_c134_of_exclHyp_corrM hx⟩

theorem input15122HSRuLocalCorr_of_combined (h : Input15122HSRuModels) :
    Input15122HSRuLocalCorr :=
  input15122HSRuLocalCorr_of_models h.1 h.2

theorem input15122HSRuLocalCorrM_of_combined (h : Input15122HSRuModels) :
    Input15122HSRuLocalCorrM :=
  input15122HSRuLocalCorrM_of_models h.1 h.2

theorem input15122ThreeDHSRu_of_local_corrM
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (hC34 : C134L32CorrM) (h1416 : StageLemma1416)
    (hloc : Input15122HSRuLocalCorrM) : Input15122ThreeDHSRu := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp h3D hx18 hHR
  have hq := hc.ctx.qtfe
  have hMf := hc.ctx.mf
  have hSet := hc.ctx.setting
  set S := s1516 T Z₁ with hSdef
  have hLG : L ≤ g1_1516 Z₁ := le_of_mem_cComp hc.hL.comp
  have hS2 : IsPGroup 2 ↥S := hc.h18.four.2.1
  have hsyl : IsSylowTwoOf (S ⊓ L) L := hc.h20.sylow
  have hSN : S ≤ Subgroup.normalizer (L : Set G) := by
    rcases lemma_1_2_1_three hq.qtke hq.simple hq.nonabelian h37 h38
        (hSet.pCore_g1_ne_bot hq hMf) hc.hL.comp with hn | ⟨-, h2⟩
    · exact (s1516_le_g1 T Z₁).trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hLG).mp hn)
    · exact absurd h2 (hsru_not_a38Types hHR)
  have hZ : IsPGroup 2 ↥(Subgroup.center ↥L) := (hc.h20.three hcomp).1
  have hLnot : ¬ L ≤ Subgroup.centralizer (centerOf (S ⊓ L) : Set G) := by
    intro hle
    apply hc.hL.not_le
    have h1 : L ⊓ Subgroup.centralizer (centerOf (S ⊓ L) : Set G) = L := inf_eq_left.mpr hle
    have h2 : mZ1516 Mc Z₁ ⊓ L = L := h3D.2.trans h1
    exact h2 ▸ inf_le_left
  obtain ⟨K, hKL, hKS, hKcomp, hKsyl, hKchar, ⟨α, hα⟩, hKnot, hnoC⟩ :=
    hloc G L S hcomp.2.2 hZ hHR hS2 hSN hsyl hLnot
  have hKG : K ≤ g1_1516 Z₁ := hKL.trans hLG
  have hKSG : K ⊔ S ≤ g1_1516 Z₁ := sup_le hKG (s1516_le_g1 T Z₁)
  have hpc : pCoreOf 2 (K ⊔ S) ≠ ⊥ := by
    have h1 : pCoreOf 2 (g1_1516 Z₁) ≤ S := hc.h18.four.pCoreOf_le
    have h2 : pCoreOf 2 (g1_1516 Z₁) ≤ pCoreOf 2 (K ⊔ S) :=
      le_pCoreOf_of_le_normalizer 2 (h1.trans le_sup_right)
        (hKSG.trans (le_normalizer_pCoreOf 2 (g1_1516 Z₁)))
        (pCoreOf_isPGroup 2 (g1_1516 Z₁))
    exact ne_bot_of_le_ne_bot (hSet.pCore_g1_ne_bot hq hMf) h2
  have hSQ : IsSQTKIn (K ⊔ S) :=
    ⟨stronglyQuasithin_of_pCoreOf_ne_bot hq.qtke hpc,
      kGroup_of_pCoreOf_ne_bot hq.qtke hq.simple hq.nonabelian hpc⟩
  have hchar : CharTwo (K ⊔ S) := zb_charTwo_sup hKS hS2 hKchar
  have hset : ((K ⊔ S : Subgroup G) : Set G) = (K : Set G) * (S : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left K S hKS
  have hLie := SBd7.isRankTwoLie2Derived_of_modO2 α hα.1 hα.2
  have hS0 : S ≠ ⊥ := ne_bot_of_le_ne_bot (hSet.pCore_g1_ne_bot hq hMf) hc.h18.four.pCoreOf_le
  have hKperf : ⁅K, K⁆ = K := hKcomp.2.1
  by_cases hno : ∀ C : Subgroup G, C ≤ S → C ≠ ⊥ → (C.subgroupOf S).Characteristic →
      ¬ (K ⊔ S ≤ Subgroup.normalizer (C : Set G))
  ·
    have hMSp : IsMSPair (K ⊔ S) S :=
      S151S9.isMSPair_of_noChar hSQ hchar hKcomp hset hLie hKsyl hS0 hno
    obtain ⟨i, hi⟩ := hC34 G (K ⊔ S) S K hMSp hKcomp hset
      ⟨ZMod 2, inferInstance, inferInstance, α, ZMod.card 2, hα⟩
    exact hnoC i hi
  ·
    push Not at hno
    obtain ⟨C, hCS, hC0, hCchar, hKSC⟩ := hno
    have hTC : T ≤ Subgroup.normalizer (C : Set G) :=
      S151S9.le_normalizer_of_char hCS hCchar hx18.s_normal
    have hC2 : IsPGroup 2 ↥C := hS2.to_le hCS
    have hCN : C ≤ Subgroup.normalizer (C : Set G) := Subgroup.le_normalizer
    have hCpc : C ≤ pCoreOf 2 (Subgroup.normalizer (C : Set G)) :=
      le_pCoreOf_of_le_normalizer 2 hCN le_rfl hC2
    have hInH : InH T (Subgroup.normalizer (C : Set G)) :=
      ⟨hTC, ne_bot_of_le_ne_bot hC0 hCpc⟩
    obtain ⟨hperf1, hMc⟩ := (h1416 G T Mc hq).2.2.2 _ hInH
    have hKN : K ≤ Subgroup.normalizer (C : Set G) := le_sup_left.trans hKSC
    have hKinf : K ≤ perfectCore (Subgroup.normalizer (C : Set G)) :=
      le_perfectCore_of_perfect hKN hKperf
    have hKMZ : K ≤ mZ1516 Mc Z₁ ⊓ L := fun x hx =>
      ⟨⟨hKG hx, hMc (hperf1 (hKinf hx))⟩, hKL hx⟩
    rw [h3D.2] at hKMZ
    exact hKnot fun x hx => (hKMZ hx).2

end CFSG.Quasithin
