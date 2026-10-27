module

public import CFSG.LieType.Steinberg.CentralExt.PSLSmall
public import CFSG.Quasithin.Recognition.F112WChief
public import CFSG.Quasithin.EmptyFaithful.S153E58B
public import CFSG.CGT.Timmesfeld75.Lemma27
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped commutatorElement

namespace Sec526

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_isL2Quot {L : Subgroup G} {N : Type*} [Group N] [Finite N] {n f : ℕ}
    (hn : 2 ≤ n) (hfn : f < 2 * n) (hperf : Group.IsPerfect ↥L) (hL : IsL2Quot n (oTwoQuot ↥L))
    (ρ : ↥L →* MulAut N) (hN : Nat.card N = 2 ^ f) : ρ = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := hL
  set π : ↥L →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Open.pCore 2 ↥L)) with hπ
  have hπs : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπker : π.ker = Open.pCore 2 ↥L := by
    ext x
    rw [MonoidHom.mem_ker, hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have h4 : 4 ≤ Nat.card (GaloisField 2 n) := by
    rw [GaloisField.card 2 n (by omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  have : (ρ.ker.map π).Normal := (MonoidHom.normal_ker ρ).map π hπs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ρ.ker.map π) with hb | ht
  ·
    exfalso
    have hKO : ρ.ker ≤ π.ker := by
      intro x hx
      rw [MonoidHom.mem_ker]
      have : π x ∈ ρ.ker.map π := ⟨x, hx, rfl⟩
      rw [hb] at this
      exact this
    let θ : ↥L ⧸ ρ.ker →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n) :=
      QuotientGroup.lift ρ.ker π hKO
    have hθ : Function.Surjective θ := by
      intro y
      obtain ⟨x, rfl⟩ := hπs y
      exact ⟨QuotientGroup.mk x, rfl⟩
    have hρ := QuotientGroup.kerLift_injective ρ
    have hdvd := Subgroup.card_dvd_of_surjective hθ
    rw [card_psl_two_gf2 n (by omega)] at hdvd
    by_cases hn3 : n = 3
    · subst hn3
      have := CGT.Timmesfeld75.lemma27_psl2_eight θ hθ (QuotientGroup.kerLift ρ) hρ hN
      omega
    · have h4n : (2 ^ n) ^ 2 = 4 ^ n := by
        rw [← pow_mul, mul_comm, pow_mul]
        norm_num
      have := CGT.Timmesfeld75.lemma27_psl2 hn hn3 (by rw [h4n]; exact hdvd)
        (QuotientGroup.kerLift ρ) hρ hN
      omega
  ·
    have hrange : ρ.range = (Open.pCore 2 ↥L).map ρ := by
      refine le_antisymm ?_ (Subgroup.map_le_range ρ _)
      rintro _ ⟨x, rfl⟩
      have : π x ∈ ρ.ker.map π := by rw [ht]; exact Subgroup.mem_top _
      obtain ⟨k, hk, hkx⟩ := this
      have hxk : k⁻¹ * x ∈ Open.pCore 2 ↥L := by
        rw [← hπker, MonoidHom.mem_ker, map_mul, map_inv, hkx, inv_mul_cancel]
      refine ⟨k⁻¹ * x, hxk, ?_⟩
      rw [map_mul, map_inv, MonoidHom.mem_ker.mp hk, inv_one, one_mul]
    have hp : IsPGroup 2 ↥ρ.range := by
      rw [hrange]
      exact (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥L) 2).map ρ
    have hperfR : Group.IsPerfect ↥ρ.range :=
      Group.IsPerfect.ofSurjective (f := ρ.rangeRestrict) ρ.rangeRestrict_surjective
    have hbot : ρ.range = ⊥ := by
      by_contra hne
      have : Nontrivial ↥ρ.range := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
      exact Group.IsPerfect.not_isNilpotent ↥ρ.range hp.isNilpotent
    ext x
    have hx : ρ x ∈ ρ.range := ⟨x, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hx
    rw [hx]
    rfl

omit [Finite G] in
theorem commutator_eq_bot_of_perfect {A L : Subgroup G} (hperf : ⁅L, L⁆ = L)
    (h : ⁅⁅A, L⁆, L⁆ = ⊥) : ⁅A, L⁆ = ⊥ := by
  have h1 : ⁅⁅L, A⁆, L⁆ = ⊥ := by rw [Subgroup.commutator_comm L A]; exact h
  have h2 : ⁅⁅L, L⁆, A⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h
  rw [hperf] at h2
  rw [Subgroup.commutator_comm]
  exact h2

theorem commutator_le_of_isL2Quot {L N W : Subgroup G} {n f : ℕ} (hn : 2 ≤ n) (hfn : f < 2 * n)
    (hperf : Group.IsPerfect ↥L) (hL : IsL2Quot n (oTwoQuot ↥L))
    (hLN : L ≤ Subgroup.normalizer (N : Set G)) (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hWN : W ≤ N) [hWn : (W.subgroupOf N).Normal]
    (hcard : Nat.card N = 2 ^ f * Nat.card W) : ⁅N, L⁆ ≤ W := by
  classical
  set ρ₀ : ↥L →* MulAut ↥N := (Subgroup.normalizerMonoidHom N).comp (Subgroup.inclusion hLN)
    with hρ₀
  have hρ₀v : ∀ (l : ↥L) (x : ↥N), ((ρ₀ l x : ↥N) : G) = l * x * (l : G)⁻¹ := fun l x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe N _ x
  set W' := W.subgroupOf N with hW'
  have hmem : ∀ (l : ↥L) (y : ↥N), y ∈ W' → ρ₀ l y ∈ W' := by
    intro l y hy
    rw [Subgroup.mem_subgroupOf, hρ₀v]
    exact (Subgroup.mem_normalizer_iff.mp (hLW l.2) y).mp (Subgroup.mem_subgroupOf.mp hy)
  have hinv : ∀ l, W'.map (ρ₀ l : ↥N →* ↥N) = W' := by
    intro l
    refine le_antisymm ?_ fun y hy => ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact hmem l y hy
    · refine ⟨ρ₀ l⁻¹ y, hmem l⁻¹ y hy, ?_⟩
      change ρ₀ l (ρ₀ l⁻¹ y) = y
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  set ρ := SL2MinimalFaithful.quotientAction ρ₀ W' hinv with hρ
  have hcardW : Nat.card W' = Nat.card W :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWN).toEquiv
  have hcardQ : Nat.card (↥N ⧸ W') = 2 ^ f := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup W'
    rw [hcardW, hcard] at h
    have hpos : 0 < Nat.card W := Nat.card_pos
    exact (Nat.eq_of_mul_eq_mul_right hpos h).symm
  have h1 := eq_one_of_isL2Quot hn hfn hperf hL ρ hcardQ
  rw [Subgroup.commutator_le]
  intro x hx l hl
  have h2 : ρ ⟨l, hl⟩ (QuotientGroup.mk ⟨x, hx⟩ : ↥N ⧸ W') = QuotientGroup.mk ⟨x, hx⟩ := by
    rw [h1, MonoidHom.one_apply, MulAut.one_apply]
  rw [hρ, SL2MinimalFaithful.quotientAction_mk, QuotientGroup.eq] at h2
  have h3 : ((ρ₀ ⟨l, hl⟩ ⟨x, hx⟩)⁻¹ * ⟨x, hx⟩ : ↥N) ∈ W' := h2
  rw [Subgroup.mem_subgroupOf] at h3
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hρ₀v] at h3
  have h4 : x * ((l * x * l⁻¹)⁻¹ * x) * x⁻¹ ∈ W :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer_of_normal_subgroupOf hWN hx) _).mp h3
  have h5 : ⁅x, l⁆ = x * ((l * x * l⁻¹)⁻¹ * x) * x⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [h5]
  exact h4

theorem card_hopfMultiplier_psl_two_le
    {n : ℕ} (hn : 2 ≤ n) :
    Finite (CFSG.RankThree.PerfectCover.hopfMultiplier
        (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n))) ∧
      Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
        (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n))) ≤ 2 := by
  have e₀ := (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess
    (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n))).symm
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  · obtain rfl : n = 2 := by omega
    obtain ⟨-, ⟨e⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SLClosed.psl_two_four_hopfMultiplier
    refine ⟨Finite.of_equiv _ (e₀.trans e).symm.toEquiv, ?_⟩
    rw [Nat.card_congr (e₀.trans e).toEquiv, Nat.card_eq_fintype_card,
      Fintype.card_multiplicative, ZMod.card]
  · have : Fintype (GaloisField 2 n) := Fintype.ofFinite _
    have hcard : Fintype.card (GaloisField 2 n) = 2 ^ n := by
      rw [← Nat.card_eq_fintype_card, GaloisField.card 2 n (by omega)]
    have h8 : 8 ≤ 2 ^ n := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
    have h9 : 2 ^ n ≠ 9 := by
      intro h
      have : 2 ∣ 9 := h ▸ dvd_pow_self 2 (by omega)
      omega
    obtain ⟨-, ⟨e⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SLClosed.psl_two_hopfMultiplier_of_mulEquiv
      (k := GaloisField 2 n) (by rw [hcard]; omega) (by rw [hcard]; exact h9) (MulEquiv.refl _)
    have hpos : 0 < Nat.gcd 2 (Fintype.card (GaloisField 2 n) - 1) :=
      Nat.gcd_pos_of_pos_left _ (by norm_num)
    have : NeZero (Nat.gcd 2 (Fintype.card (GaloisField 2 n) - 1)) := ⟨hpos.ne'⟩
    refine ⟨Finite.of_equiv _ (e₀.trans e).symm.toEquiv, ?_⟩
    rw [Nat.card_congr (e₀.trans e).toEquiv, Nat.card_eq_fintype_card,
      Fintype.card_multiplicative, ZMod.card]
    exact Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)

omit [Finite G] in
theorem not_commutator_le_of_isL2Quot
    {L R₀ : Subgroup G} {n : ℕ} (hn : 2 ≤ n) (hperf : Group.IsPerfect ↥L)
    (hL : IsL2Quot n (oTwoQuot ↥L)) (hR₀ : R₀ ≤ pCoreOf 2 L)
    (hLR : L ≤ Subgroup.normalizer (R₀ : Set G))
    (hcard : 2 * Nat.card R₀ < Nat.card (pCoreOf 2 L)) : ¬ ⁅pCoreOf 2 L, L⁆ ≤ R₀ := by
  intro hc
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := hL
  set P : Subgroup ↥L := Open.pCore 2 ↥L with hP
  have hR₀L : R₀ ≤ L := hR₀.trans (pCoreOf_le 2 L)
  set R' : Subgroup ↥L := R₀.subgroupOf L with hR'
  have hR'n : R'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hR₀L).mpr hLR
  have hmemP : ∀ x : ↥L, (x : G) ∈ pCoreOf 2 L → x ∈ P := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  have hR'P : R' ≤ P := fun x hx => hmemP x (hR₀ (Subgroup.mem_subgroupOf.mp hx))
  set q₀ : ↥L ⧸ R' →* ↥L ⧸ P := QuotientGroup.map R' P (MonoidHom.id _)
    (by rw [Subgroup.comap_id]; exact hR'P) with hq₀
  set q : ↥L ⧸ R' →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n) :=
    e.toMonoidHom.comp q₀ with hqdef
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨x, hx⟩ := e.surjective y
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨QuotientGroup.mk l, by rw [← hx]; rfl⟩
  have hker : ∀ l : ↥L, (QuotientGroup.mk l : ↥L ⧸ R') ∈ q.ker ↔ l ∈ P := by
    intro l
    rw [MonoidHom.mem_ker, hqdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, hq₀, QuotientGroup.map_mk, MonoidHom.id_apply,
      QuotientGroup.eq_one_iff]
  have hcen : q.ker ≤ Subgroup.center (↥L ⧸ R') := by
    intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have hxP : x ∈ P := (hker x).mp hy
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have hxQ : (x : G) ∈ pCoreOf 2 L := ⟨x, hxP, rfl⟩
    have hcomm : ⁅(x⁻¹ : G), ((l : ↥L)⁻¹ : G)⁆ ∈ R₀ :=
      hc (Subgroup.commutator_mem_commutator ((pCoreOf 2 L).inv_mem hxQ) (L.inv_mem l.2))
    rw [Subgroup.mem_subgroupOf]
    have h1 : (((l * x)⁻¹ * (x * l) : ↥L) : G) = ⁅(x⁻¹ : G), ((l : ↥L)⁻¹ : G)⁆ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rw [h1]
    exact hcomm
  have : Group.IsPerfect (↥L ⧸ R') :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' R') (QuotientGroup.mk'_surjective R')
  have hsurj := CFSG.RankThree.PerfectCover.hopfMultiplierToKer_surjective q hq hcen
  obtain ⟨hMfin, hMcard⟩ := card_hopfMultiplier_psl_two_le hn
  have hK : Nat.card q.ker ≤ 2 := (Nat.card_le_card_of_surjective _ hsurj).trans hMcard
  set φ : ↥P →* ↥L ⧸ R' := (QuotientGroup.mk' R').comp P.subtype with hφ
  have hφker : φ.ker = R'.subgroupOf P := by
    ext x
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rfl
  have hφrange : φ.range = q.ker := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (hker x).mpr x.2
    · intro hy
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
      exact ⟨⟨x, (hker x).mp hy⟩, rfl⟩
  have h1 : Nat.card φ.ker * φ.ker.index = Nat.card ↥P := φ.ker.card_mul_index
  rw [Subgroup.index_ker, hφker] at h1
  have h2 : Nat.card ↥(R'.subgroupOf P) = Nat.card R₀ := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR'P).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR₀L).toEquiv]
  have h3 : Nat.card ↥P = Nat.card (pCoreOf 2 L) := by
    rw [pCoreOf, Nat.card_congr ((P.equivMapOfInjective L.subtype L.subtype_injective)).toEquiv]
  rw [h2, h3, hφrange] at h1
  have : Nat.card (pCoreOf 2 L) ≤ 2 * Nat.card R₀ := by
    rw [← h1]
    nlinarith
  omega

omit [Finite G] in
theorem commutator_mem_normalizer {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  rw [CFSG.LieType.Steinberg.mem_normalizer_iff_map_conj] at hA hB ⊢
  rw [Subgroup.map_commutator, hA, hB]

omit [Finite G] in
theorem eq_zero_of_isChiefSeriesBetween_self {H U W : Subgroup G} {n : ℕ}
    (h : F112W.IsChiefSeriesBetween H U W W n) : n = 0 := by
  cases h with
  | refl => rfl
  | central hstep _ hs => exact absurd (hs.le.trans_lt hstep.2.2.1) (lt_irrefl _)
  | noncentral hstep _ hs => exact absurd (hs.le.trans_lt hstep.2.2.1) (lt_irrefl _)

omit [Finite G] in
theorem le_one_of_isChiefSeriesBetween_irred {H U W N : Subgroup G} {n : ℕ}
    (h : F112W.IsChiefSeriesBetween H U W N n)
    (hirr : ∀ K : Subgroup G, IsNormalIn H U K → W ≤ K → K ≤ N → K = W ∨ K = N) : n ≤ 1 := by
  cases h with
  | refl => omega
  | @central N L n hstep _ hs =>
    rcases hirr L hstep.2.1 hs.le hstep.2.2.1.le with rfl | rfl
    · have := eq_zero_of_isChiefSeriesBetween_self hs
      omega
    · exact absurd hstep.2.2.1 (lt_irrefl _)
  | @noncentral N L n hstep _ hs =>
    rcases hirr L hstep.2.1 hs.le hstep.2.2.1.le with rfl | rfl
    · have := eq_zero_of_isChiefSeriesBetween_self hs
      omega
    · exact absurd hstep.2.2.1 (lt_irrefl _)

theorem eta_le_one_of_isShort2 {L : Subgroup G} (hL : IsShort2 L) :
    F112W.eta L (pCoreOf 2 L) (pCoreOf 2 L) ≤ 1 := by
  classical
  set Q := pCoreOf 2 L with hQ
  have hQL : Q ≤ L := pCoreOf_le 2 L
  have hLQ : L ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_pCoreOf 2 L
  have hQQ : Q ≤ pCoreOf 2 L := le_rfl
  have hU : blockU L = ⁅Q, L⁆ := rfl
  have hUQ : blockU L ≤ Q := F112W.commutator_le_self_of_le_normalizer hLQ
  have hZU : blockZ L ≤ blockU L := inf_le_left
  have hQn : IsNormalIn L Q Q := F112W.isNormalIn_of_le_normalizer le_rfl hLQ
  have hUn : IsNormalIn L Q (blockU L) :=
    F112W.isNormalIn_of_le_normalizer hUQ fun g hg => commutator_mem_normalizer (hLQ hg)
      (Subgroup.le_normalizer hg)
  have hZn : IsNormalIn L Q (blockZ L) := by
    refine ⟨hZU.trans hUQ, fun g hg x hx => ?_⟩
    have hxc := Subgroup.mem_centralizer_iff.mp hx.2 g hg
    rw [hxc, mul_inv_cancel_right]
    exact hx
  obtain ⟨a₁, ha₁⟩ := F112W.exists_isChiefSeriesBetween hUn Q hQn hUQ
  have ha₁0 : a₁ = 0 := F112W.count_eq_zero_of_commutator_le hQL hQQ ha₁
    ((Subgroup.commutator_mono le_rfl (oTwoUpper_le L)).trans le_rfl)
  have h1 := F112W.eta_eq_add hQL hUn ha₁
  obtain ⟨a₂, ha₂⟩ := F112W.exists_isChiefSeriesBetween hZn (blockU L) hUn hZU
  have ha₂1 : a₂ ≤ 1 := le_one_of_isChiefSeriesBetween_irred ha₂ fun K hK hZK hKU =>
    hL.2.2.2.2.2 K hZK hKU (D14.le_normalizer_of_isNormalIn hK)
  have h2 := F112W.eta_eq_add hQL hZn ha₂
  have h3 : F112W.eta L Q (blockZ L) = 0 := by
    rw [F112W.eta_eq_zero_iff hQL hQQ hZn, eq_bot_iff]
    refine (Subgroup.commutator_mono le_rfl (oTwoUpper_le L)).trans ?_
    rw [Subgroup.commutator_le]
    intro x hx g hg
    have hxc := Subgroup.mem_centralizer_iff.mp hx.2 g hg
    rw [commutatorElement_def, ← hxc, mul_inv_cancel_right, mul_inv_cancel]
    exact Subgroup.one_mem _
  omega

theorem two_le_eta {L R₀ : Subgroup G} (hperf : ⁅L, L⁆ = L) (hR₀ : R₀ ≤ pCoreOf 2 L)
    (hLR : L ≤ Subgroup.normalizer (R₀ : Set G)) (h1 : ⁅R₀, L⁆ ≠ ⊥)
    (h2 : ¬ ⁅pCoreOf 2 L, L⁆ ≤ R₀) : 2 ≤ F112W.eta L (pCoreOf 2 L) (pCoreOf 2 L) := by
  classical
  set Q := pCoreOf 2 L with hQ
  have hQL : Q ≤ L := pCoreOf_le 2 L
  have hLQ : L ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_pCoreOf 2 L
  have hO : oTwoUpper L = L := S153E58.oTwoUpper_eq_of_perfect hperf
  have hQn : IsNormalIn L Q Q := F112W.isNormalIn_of_le_normalizer le_rfl hLQ
  have hRn : IsNormalIn L Q R₀ := F112W.isNormalIn_of_le_normalizer hR₀ hLR
  obtain ⟨a, ha⟩ := F112W.exists_isChiefSeriesBetween hRn Q hQn hR₀
  have h3 := F112W.eta_eq_add hQL hRn ha
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply h2
    have := (F112W.isChiefSeriesBetween_zero_iff hQL le_rfl hRn hQn hR₀).mp ha
    rwa [hO] at this
  have hb0 : F112W.eta L Q R₀ ≠ 0 := by
    intro h0
    apply h1
    have := (F112W.eta_eq_zero_iff hQL le_rfl hRn).mp h0
    rwa [hO] at this
  omega

theorem not_isShort2_of_two {L R₀ : Subgroup G} (hperf : ⁅L, L⁆ = L) (hR₀ : R₀ ≤ pCoreOf 2 L)
    (hLR : L ≤ Subgroup.normalizer (R₀ : Set G)) (h1 : ⁅R₀, L⁆ ≠ ⊥)
    (h2 : ¬ ⁅pCoreOf 2 L, L⁆ ≤ R₀) : ¬ IsShort2 L := fun hs => by
  have := two_le_eta hperf hR₀ hLR h1 h2
  have := eta_le_one_of_isShort2 hs
  omega

end Sec526

end CFSG.Quasithin.H13
