module

public import CFSG.Quasithin.Background.G11BridgeSQTK
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem exists_ne_zero_fixed_of_isPGroup [Finite V] [Nontrivial V] (P : Subgroup (GLV V))
    (hP : IsPGroup 2 ↥P) : ∃ v : V, v ≠ 0 ∧ ∀ g ∈ P, g v = v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := hP.card_modEq_card_fixedPoints V
  by_contra hcon
  push Not at hcon
  have hfix : ∀ v ∈ MulAction.fixedPoints ↥P V, v = 0 := by
    intro v hv
    by_contra hv0
    obtain ⟨g, hg, hgv⟩ := hcon v hv0
    exact hgv (MulAction.mem_fixedPoints.1 hv ⟨g, hg⟩)
  have h1 : Nat.card ↑(MulAction.fixedPoints ↥P V) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun a b => Subtype.ext ((hfix a a.2).trans (hfix b b.2).symm)⟩,
      ⟨⟨0, MulAction.mem_fixedPoints.2 fun g => smul_zero g⟩⟩⟩
  have h2 : 2 ∣ Nat.card V := by
    have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V), Nat.card_zmod]
    exact dvd_pow_self 2 Module.finrank_pos.ne'
  rw [h1] at hmod
  have h3 : Nat.card V % 2 = 1 := hmod
  have h4 := Nat.mod_eq_zero_of_dvd h2
  omega

theorem pCoreOf_eq_bot_of_isIrr_top [Finite V] {K : Subgroup (GLV V)} (hK : IsIrr K ⊤) :
    pCoreOf 2 K = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (GLV V) := Finite.of_injective _ DFunLike.coe_injective
  have hP2 : IsPGroup 2 ↥(Open.pCore 2 ↥K) := CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hPn : (Open.pCore 2 ↥K).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  set N : Subgroup (GLV V) := (Open.pCore 2 ↥K).map K.subtype with hN
  have hN2 : IsPGroup 2 ↥N :=
    hP2.of_surjective ((Open.pCore 2 ↥K).equivMapOfInjective K.subtype K.subtype_injective).toMonoidHom
      ((Open.pCore 2 ↥K).equivMapOfInjective K.subtype K.subtype_injective).surjective
  have hNn : ∀ γ ∈ K, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N := by
    rintro γ hγ _ ⟨p, hp, rfl⟩
    exact ⟨⟨γ, hγ⟩ * p * ⟨γ, hγ⟩⁻¹, hPn.conj_mem p hp ⟨γ, hγ⟩, rfl⟩
  have hinv : Invariant K (fixedSpace N) := invariant_fixedSpace hNn
  have hnt : Nontrivial V := by
    obtain ⟨x, -, hx⟩ := (Submodule.ne_bot_iff _).1 hK.ne_bot
    exact nontrivial_of_ne x 0 hx
  obtain ⟨v, hv0, hv⟩ := exists_ne_zero_fixed_of_isPGroup N hN2
  rcases hK.eq_bot_or_eq hinv le_top with h | h
  · exfalso
    have : v ∈ fixedSpace N := hv
    rw [h, Submodule.mem_bot] at this
    exact hv0 this
  · rw [fixedSpace_eq_top_iff] at h
    rw [pCoreOf, ← hN, eq_bot_iff]
    intro n hn
    rw [Subgroup.mem_bot]
    exact h n hn

@[expose] noncomputable def restrictRange (K : Subgroup (GLV V)) (I : Submodule (ZMod 2) V)
    (hI : Invariant K I) : Subgroup (GLV ↥I) :=
  (restrictHom K I hI).range

section Restrict

variable {K : Subgroup (GLV V)} {I : Submodule (ZMod 2) V}

theorem restrictEquiv_mem_restrictRange (hI : Invariant K I) {k : GLV V} (hk : k ∈ K) :
    restrictEquiv k I (hI.conjSub_eq hk) ∈ restrictRange K I hI :=
  ⟨⟨k, hk⟩, rfl⟩

theorem isQuotientOfSQTKTauCeti_restrictRange (hI : Invariant K I)
    (hq : IsQuotientOfSQTKTauCeti ↥K) : IsQuotientOfSQTKTauCeti ↥(restrictRange K I hI) :=
  hq.of_surjective (restrictHom K I hI).rangeRestrict (MonoidHom.rangeRestrict_surjective _)

theorem isIrr_restrictRange_top (hI : IsIrr K I) : IsIrr (restrictRange K I hI.1) ⊤ := by
  refine ⟨invariant_top _, ?_⟩
  have : Nontrivial ↥I := Submodule.nontrivial_iff_ne_bot.2 hI.ne_bot
  refine ⟨bot_lt_top, fun J hJ _ _ => ?_⟩
  have hJ' : Invariant K (J.map I.subtype) := by
    rintro k hk _ ⟨j, hj, rfl⟩
    exact ⟨restrictEquiv k I (hI.1.conjSub_eq hk) j,
      hJ _ (restrictEquiv_mem_restrictRange hI.1 hk) j hj, rfl⟩
  rcases hI.eq_bot_or_eq hJ' (Submodule.map_subtype_le I J) with h | h
  · left
    rw [Submodule.eq_bot_iff]
    intro x hx
    have : (x : V) ∈ J.map I.subtype := ⟨x, hx, rfl⟩
    rw [h, Submodule.mem_bot] at this
    exact Subtype.ext this
  · right
    rw [eq_top_iff]
    intro x _
    have : (x : V) ∈ J.map I.subtype := by rw [h]; exact x.2
    obtain ⟨j, hj, hjx⟩ := this
    have : j = x := Subtype.ext hjx
    rw [← this]
    exact hj

@[expose] noncomputable def commMap (a : GLV V) (I : Submodule (ZMod 2) V) (h : conjSub a I = I) :
    ↥I →ₗ[ZMod 2] ↥I :=
  (restrictEquiv a I h : ↥I →ₗ[ZMod 2] ↥I) - LinearMap.id

theorem coe_commMap {a : GLV V} (h : conjSub a I = I) (i : ↥I) :
    ((commMap a I h i : ↥I) : V) = a (i : V) - i := rfl

theorem inducesTransvection_iff_finrank [Finite V] {a : GLV V} (h : conjSub a I = I) :
    (∃ c : V, InducesTransvection a I c) ↔
      Module.finrank (ZMod 2) (LinearMap.range (commMap a I h)) = 1 := by
  set R := LinearMap.range (commMap a I h) with hR
  constructor
  · rintro ⟨c, hc, u, hu, hau⟩
    have hle : R ≤ (Submodule.span (ZMod 2) {c}).comap I.subtype := by
      rintro _ ⟨i, rfl⟩
      exact hc i i.2
    have h1 : Module.finrank (ZMod 2) R ≤ 1 := by
      calc Module.finrank (ZMod 2) R
          ≤ Module.finrank (ZMod 2) ↥(Submodule.map I.subtype R) :=
            (LinearEquiv.finrank_eq
              (Submodule.equivMapOfInjective I.subtype I.injective_subtype R)).le
        _ ≤ Module.finrank (ZMod 2) ↥(Submodule.span (ZMod 2) {c}) :=
            Submodule.finrank_mono (Submodule.map_le_iff_le_comap.2 hle)
        _ ≤ 1 := by
            have := finrank_span_le_card (R := ZMod 2) ({c} : Set V)
            simpa using this
    have h2 : R ≠ ⊥ := by
      intro hbot
      have : commMap a I h ⟨u, hu⟩ ∈ R := ⟨⟨u, hu⟩, rfl⟩
      rw [hbot, Submodule.mem_bot] at this
      apply hau
      have := congrArg Subtype.val this
      exact sub_eq_zero.1 this
    have h3 : Module.finrank (ZMod 2) R ≠ 0 := by
      intro h0
      exact h2 (Submodule.finrank_eq_zero.1 h0)
    omega
  · intro h1
    obtain ⟨c, hc0, hc⟩ := finrank_eq_one_iff'.1 h1
    refine ⟨((c : R) : ↥I), fun u hu => ?_, ?_⟩
    · have : commMap a I h ⟨u, hu⟩ ∈ R := ⟨⟨u, hu⟩, rfl⟩
      obtain ⟨s, hs⟩ := hc ⟨_, this⟩
      refine Submodule.mem_span_singleton.2 ⟨s, ?_⟩
      have := congrArg (fun x : R => ((x : ↥I) : V)) hs
      simpa [coe_commMap] using this
    · by_contra hcon
      push Not at hcon
      apply hc0
      have : (c : ↥I) = 0 := by
        obtain ⟨i, hi⟩ := c.2
        have : commMap a I h i = 0 := by
          apply Subtype.ext
          have := hcon i i.2
          rw [coe_commMap]
          exact sub_eq_zero.2 this
        rw [← hi, this]
      exact Subtype.ext this

theorem invariant_iSup_conjSub (K : Subgroup (GLV V)) (R : Submodule (ZMod 2) V) :
    Invariant K (⨆ g ∈ K, conjSub g R) := by
  rw [invariant_iff_conjSub_le]
  intro k hk
  rw [conjSub, Submodule.map_iSup]
  refine iSup_le fun g => ?_
  rw [Submodule.map_iSup]
  refine iSup_le fun hg => ?_
  have : Submodule.map (k : V →ₗ[ZMod 2] V) (conjSub g R) = conjSub (k * g) R :=
    (conjSub_mul k g R).symm
  rw [this]
  exact le_iSup₂_of_le (k * g) (K.mul_mem hk hg) le_rfl

theorem fixes_of_commute_sq_eq_one (hI : IsIrr K I) {y : GLV V} (hy2 : y * y = 1)
    (hyI : conjSub y I = I) (hcomm : ∀ k ∈ K, ∀ i ∈ I, y (k i) = k (y i)) :
    ∀ i ∈ I, y i = i := by
  let C : Submodule (ZMod 2) V := I ⊓ LinearMap.ker ((y : V →ₗ[ZMod 2] V) - LinearMap.id)
  have hmemC : ∀ i : V, i ∈ C ↔ i ∈ I ∧ y i = i := fun i => by
    simp [C, LinearMap.mem_ker, sub_eq_zero]
  have hinv : Invariant K C := by
    intro k hk i hi
    obtain ⟨hiI, hyi⟩ := (hmemC i).1 hi
    refine (hmemC _).2 ⟨hI.1 k hk i hiI, ?_⟩
    rw [hcomm k hk i hiI, hyi]
  have hy2' : ∀ v : V, y (y v) = v := fun v => by
    have := congrArg (fun e : GLV V => e v) hy2
    exact this
  have hdouble : ∀ x : V, x + x = 0 := fun x => by
    rw [← two_smul (ZMod 2) x]
    have : (2 : ZMod 2) = 0 := by decide
    rw [this, zero_smul]
  have hj : ∀ i ∈ I, y i - i ∈ C := fun i hi => by
    refine (hmemC _).2 ⟨I.sub_mem (by
      have : y i ∈ conjSub y I := apply_mem_conjSub hi
      rwa [hyI] at this) hi, ?_⟩
    rw [map_sub, hy2']
    have h3 := eq_neg_of_add_eq_zero_left (hdouble (y i - i))
    rw [neg_sub] at h3
    exact h3.symm
  rcases hI.eq_bot_or_eq hinv inf_le_left with h0 | h1
  · exfalso
    apply hI.ne_bot
    rw [Submodule.eq_bot_iff]
    intro i hi
    have hji := hj i hi
    rw [h0, Submodule.mem_bot, sub_eq_zero] at hji
    have : i ∈ C := (hmemC i).2 ⟨hi, hji⟩
    rw [h0, Submodule.mem_bot] at this
    exact this
  · intro i hi
    have : i ∈ C := by rw [h1]; exact hi
    exact ((hmemC i).1 this).2

end Restrict

end G11

end CFSG.Quasithin
