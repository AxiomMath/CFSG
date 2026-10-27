module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartOne.K159.SzAbs

open MulAut
open scoped Pointwise

theorem card_orbit_of_free {Q X : Type*} [Group Q] [MulAction Q X] (x : X)
    (hfree : ∀ q : Q, ∀ x : X, q • x = x → q = 1) :
    Nat.card (MulAction.orbit Q x) = Nat.card Q := by
  have hs : MulAction.stabilizer Q x = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro q hq
    exact hfree q x hq
  rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer Q x), hs]
  exact Nat.card_congr QuotientGroup.quotientBot.toEquiv

open MulAction in
theorem card_dvd_of_free {Q X : Type*} [Group Q] [MulAction Q X] [Finite X]
    (hfree : ∀ q : Q, ∀ x : X, q • x = x → q = 1) : Nat.card Q ∣ Nat.card X := by
  classical
  have : Fintype X := Fintype.ofFinite X
  have : Fintype (orbitRel.Quotient Q X) := Fintype.ofFinite _
  have h1 : Nat.card X = ∑ ω : orbitRel.Quotient Q X, Nat.card ω.orbit := by
    rw [Nat.card_congr (selfEquivSigmaOrbits' Q X), Nat.card_sigma]
  rw [h1]
  refine Finset.dvd_sum fun ω _ => ?_
  have : ω.orbit = orbit Q ω.out := orbitRel.Quotient.orbit_eq_orbit_out ω Quotient.out_eq'
  rw [this, card_orbit_of_free ω.out hfree]

theorem card_dvd_of_free_invariant {Q X : Type*} [Group Q] [MulAction Q X] [Finite X]
    (hfree : ∀ q : Q, ∀ x : X, q • x = x → q = 1) (Y : Set X)
    (hY : ∀ q : Q, ∀ y ∈ Y, q • y ∈ Y) : Nat.card Q ∣ Nat.card Y := by
  let Z : SubMulAction Q X := { carrier := Y, smul_mem' := fun q y hy => hY q y hy }
  have : Finite Z := inferInstance
  exact card_dvd_of_free (Q := Q) (X := Z) (fun q x hx => hfree q x (by
    have := congrArg Subtype.val hx
    exact this))


theorem card_ne_add_one {Ω : Type*} [Finite Ω] (ω₁ : Ω) :
    Nat.card {ω : Ω // ω ≠ ω₁} + 1 = Nat.card Ω := by
  classical
  have := Nat.card_congr (Equiv.sumCompl (fun ω : Ω => ω = ω₁))
  rw [← this, Nat.card_sum]
  have h2 : Nat.card {ω : Ω // ω = ω₁} = 1 := Nat.card_unique
  rw [h2, add_comm]

theorem card_fixed_eq_of_regular {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (U : Subgroup G) (ω₁ : Ω) (hU1 : ∀ u ∈ U, u • ω₁ = ω₁)
    (hfree : ∀ u ∈ U, ∀ ω : Ω, ω ≠ ω₁ → u • ω = ω → u = 1)
    (hcard : Nat.card U + 1 = Nat.card Ω)
    (ψ : G) (hψU : ∀ u ∈ U, ψ * u * ψ⁻¹ ∈ U) (hψ1 : ψ • ω₁ = ω₁)
    (ω₂ : Ω) (hω₂ : ω₂ ≠ ω₁) (hψ2 : ψ • ω₂ = ω₂) :
    Nat.card {ω : Ω // ψ • ω = ω} = Nat.card {u : U // ψ * u * ψ⁻¹ = u} + 1 := by
  classical
  let c : U → {ω : Ω // ω ≠ ω₁} := fun u => ⟨(u : G) • ω₂, fun h => hω₂ (by
    have h' : (u : G)⁻¹ • ((u : G) • ω₂) = (u : G)⁻¹ • ω₁ := congrArg _ h
    rw [inv_smul_smul, hU1 _ (U.inv_mem u.2)] at h'
    exact h')⟩
  have hcinj : Function.Injective c := by
    intro u u' h
    have h1 : (u : G) • ω₂ = (u' : G) • ω₂ := congrArg Subtype.val h
    have h2 : ((u : G)⁻¹ * u') • ω₂ = ω₂ := by
      rw [mul_smul, ← h1, inv_smul_smul]
    have h3 := hfree _ (U.mul_mem (U.inv_mem u.2) u'.2) ω₂ hω₂ h2
    exact Subtype.ext (inv_mul_eq_one.1 h3)
  have hcardne : Nat.card {ω : Ω // ω ≠ ω₁} = Nat.card U := by
    have h1 : Nat.card {ω : Ω // ω ≠ ω₁} + 1 = Nat.card Ω := by
      have := Nat.card_congr (Equiv.sumCompl (fun ω : Ω => ω = ω₁))
      rw [← this, Nat.card_sum]
      have h2 : Nat.card {ω : Ω // ω = ω₁} = 1 := Nat.card_unique
      rw [h2, add_comm]
    omega
  have hcbij : Function.Bijective c := hcinj.bijective_of_nat_card_le (by rw [hcardne])
  have hcψ : ∀ u : U, ψ • ((u : G) • ω₂) = ((ψ * u * ψ⁻¹ : G)) • ω₂ := by
    intro u
    calc ψ • ((u : G) • ω₂) = (ψ * u) • ω₂ := (mul_smul _ _ _).symm
      _ = ((ψ * u * ψ⁻¹) * ψ) • ω₂ := by rw [inv_mul_cancel_right]
      _ = (ψ * u * ψ⁻¹) • (ψ • ω₂) := mul_smul _ _ _
      _ = (ψ * u * ψ⁻¹) • ω₂ := by rw [hψ2]
  let f : {u : U // ψ * u * ψ⁻¹ = u} ⊕ Unit → {ω : Ω // ψ • ω = ω} := fun x =>
    match x with
    | Sum.inl u => ⟨(u.1 : G) • ω₂, by rw [hcψ, u.2]⟩
    | Sum.inr _ => ⟨ω₁, hψ1⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro (⟨u, hu⟩ | ⟨⟩) (⟨u', hu'⟩ | ⟨⟩) h
      · have h1 : (u : G) • ω₂ = (u' : G) • ω₂ := congrArg Subtype.val h
        have := hcinj (Subtype.ext h1)
        exact congrArg Sum.inl (Subtype.ext this)
      · exfalso
        have h1 : (u : G) • ω₂ = ω₁ := congrArg Subtype.val h
        exact (c u).2 h1
      · exfalso
        have h1 : ω₁ = (u' : G) • ω₂ := congrArg Subtype.val h
        exact (c u').2 h1.symm
      · rfl
    · rintro ⟨ω, hω⟩
      by_cases h1 : ω = ω₁
      · exact ⟨Sum.inr (), Subtype.ext h1.symm⟩
      · obtain ⟨u, hu⟩ := hcbij.2 ⟨ω, h1⟩
        have hu' : (u : G) • ω₂ = ω := congrArg Subtype.val hu
        refine ⟨Sum.inl ⟨u, ?_⟩, Subtype.ext hu'⟩
        have h2 : ψ • ((u : G) • ω₂) = (u : G) • ω₂ := by rw [hu']; exact hω
        rw [hcψ] at h2
        have h3 : c ⟨ψ * u * ψ⁻¹, hψU u u.2⟩ = c u := Subtype.ext h2
        exact congrArg Subtype.val (hcinj h3)
  rw [Nat.card_congr (Equiv.ofBijective f hf).symm, Nat.card_sum]
  simp

theorem card_centralizer_modEq {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (U : Subgroup G) (ψ : G) (hψ : ψ ∈ Subgroup.normalizer (U : Set G))
    (hord : ∃ k : ℕ, ψ ^ (p ^ k) = 1) :
    Nat.card {u : U // ψ * u * ψ⁻¹ = u} ≡ Nat.card U [MOD p] := by
  classical
  let σ : MulAut U := U.normalizerMonoidHom ⟨ψ, hψ⟩
  have hσ : ∀ n : ℕ, ∀ u : U, ((σ ^ n) u : G) = ψ ^ n * u * (ψ ^ n)⁻¹ := by
    intro n u
    have : σ ^ n = U.normalizerMonoidHom ((⟨ψ, hψ⟩ : Subgroup.normalizer (U : Set G)) ^ n) := by
      rw [map_pow]
    rw [this]
    simp
  obtain ⟨k, hk⟩ := hord
  have hσk : σ ^ (p ^ k) = 1 := by
    ext u
    rw [hσ, hk]
    simp
  have hΓ : IsPGroup p (Subgroup.zpowers σ) := by
    have h1 : orderOf σ ∣ p ^ k := orderOf_dvd_of_pow_eq_one hσk
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).1 h1
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hmod := hΓ.card_modEq_card_fixedPoints U
  have hfix : MulAction.fixedPoints (Subgroup.zpowers σ) U ≃ {u : U // ψ * u * ψ⁻¹ = u} := by
    refine Equiv.subtypeEquivRight fun u => ?_
    constructor
    · intro h
      have := h ⟨σ, Subgroup.mem_zpowers σ⟩
      have h2 : σ u = u := this
      have h3 := congrArg Subtype.val h2
      have := hσ 1 u
      simp only [pow_one] at this
      rw [this] at h3
      simpa using h3
    · intro h g
      have hσu : σ u = u := Subtype.ext (by
        have := hσ 1 u
        simp only [pow_one] at this
        rw [this]
        simpa using h)
      have hmem : σ ∈ MulAction.stabilizer (MulAut U) u := hσu
      have hle : Subgroup.zpowers σ ≤ MulAction.stabilizer (MulAut U) u :=
        (Subgroup.zpowers_le).2 hmem
      exact hle g.2
  rw [← Nat.card_congr hfix]
  exact hmod.symm

theorem factorization_five : (32537600 : ℕ).factorization 5 = 2 := by
  have h : (32537600 : ℕ) = 5 ^ 2 * (2 ^ 10 * 31 * 41) := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num)]
  simp only [Finsupp.add_apply]
  rw [Nat.Prime.factorization_pow (by norm_num)]
  have : ¬ 5 ∣ 2 ^ 10 * 31 * 41 := by norm_num
  rw [Nat.factorization_eq_zero_of_not_dvd this]
  simp

theorem factorization_two : (32537600 : ℕ).factorization 2 = 10 := by
  have h : (32537600 : ℕ) = 2 ^ 10 * (5 ^ 2 * 31 * 41) := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num)]
  simp only [Finsupp.add_apply]
  rw [Nat.Prime.factorization_pow (by norm_num)]
  have : ¬ 2 ∣ 5 ^ 2 * 31 * 41 := by norm_num
  rw [Nat.factorization_eq_zero_of_not_dvd this]
  simp

structure SzSylow (S : Type) [Group S] : Prop where
  card : Nat.card S = 32537600
  card_sylow : Nat.card (Sylow 2 S) = 1025
  ti : ∀ V W : Sylow 2 S, V ≠ W → (V : Subgroup S) ⊓ (W : Subgroup S) = ⊥
  cyclic : ∀ T : Sylow 5 S, IsCyclic T

theorem SzSylow.of_mulEquiv {S T : Type} [Group S] [Group T] (e : S ≃* T) (h : SzSylow T) :
    SzSylow S := by
  have h2 : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcard : Nat.card S = 32537600 := (Nat.card_congr e.toEquiv).trans h.card
  have : Finite S := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hf : Function.Surjective e.toMonoidHom := e.surjective
  have hmapinj : ∀ {p : ℕ} [Fact p.Prime], Function.Injective
      (Sylow.mapSurjective hf : Sylow p S → Sylow p T) := by
    intro p _ V W hVW
    apply Sylow.ext
    have := congrArg (fun X : Sylow p T => (X : Subgroup T)) hVW
    simp only [Sylow.coe_mapSurjective] at this
    exact Subgroup.map_injective e.injective this
  refine ⟨hcard, ?_, ?_, ?_⟩
  · rw [Nat.card_congr (Equiv.ofBijective _ ⟨hmapinj, Sylow.mapSurjective_surjective hf 2⟩)]
    exact h.card_sylow
  · intro V W hVW
    have h1 := h.ti (Sylow.mapSurjective hf V) (Sylow.mapSurjective hf W) (fun hh => hVW (hmapinj hh))
    simp only [Sylow.coe_mapSurjective] at h1
    rw [← Subgroup.map_inf _ _ (f := e.toMonoidHom) e.injective] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective (V ⊓ W) (f := e.toMonoidHom) e.injective).1 h1
  · intro V
    have h1 := h.cyclic (Sylow.mapSurjective hf V)
    simp only [Sylow.coe_mapSurjective] at h1
    exact (Subgroup.equivMapOfInjective (V : Subgroup S) e.toMonoidHom e.injective).isCyclic.2 h1

variable {H : Type} [Group H]

@[expose, instance_reducible] noncomputable def hAct (S : Subgroup H) [S.Normal] (p : ℕ) :
    MulAction H (Sylow p ↥S) :=
  MulAction.compHom (Sylow p ↥S) (MulAut.conjNormal : H →* MulAut ↥S)

theorem hAct_coe (S : Subgroup H) [S.Normal] {p : ℕ} (h : H) (V : Sylow p ↥S) :
    ((@HSMul.hSMul H (Sylow p ↥S) (Sylow p ↥S) (@instHSMul _ _ (hAct S p).toSMul) h V :
        Sylow p ↥S) : Subgroup ↥S) = (MulAut.conjNormal h : MulAut ↥S) • (V : Subgroup ↥S) := rfl

theorem smul_eq_iff_mem_normalizer {S : Subgroup H} {p : ℕ} [Fact p.Prime] (g : ↥S)
    (V : Sylow p ↥S) :
    (MulAut.conj g : MulAut ↥S) • V = V ↔ g ∈ Subgroup.normalizer (V : Set ↥S) := by
  rw [← Sylow.smul_def]
  exact Sylow.smul_eq_iff_mem_normalizer


section ActionPart

noncomputable local instance hActInst (S : Subgroup H) [S.Normal] (p : ℕ) : MulAction H (Sylow p ↥S) := hAct S p

variable {S : Subgroup H} [S.Normal] {p : ℕ}

theorem smul_coe (h : H) (V : Sylow p ↥S) :
    ((h • V : Sylow p ↥S) : Subgroup ↥S) = (MulAut.conjNormal h : MulAut ↥S) • (V : Subgroup ↥S) :=
  rfl

theorem coe_smul_eq_iff [Fact p.Prime] (s : ↥S) (V : Sylow p ↥S) :
    (s : H) • V = V ↔ s ∈ Subgroup.normalizer (V : Set ↥S) := by
  rw [← smul_eq_iff_mem_normalizer (H := H)]
  constructor
  · intro h
    apply Sylow.ext
    have := congrArg (fun W : Sylow p ↥S => (W : Subgroup ↥S)) h
    simp only [smul_coe, MulAut.conjNormal_val] at this
    rw [Sylow.pointwise_smul_def]
    exact this
  · intro h
    apply Sylow.ext
    have := congrArg (fun W : Sylow p ↥S => (W : Subgroup ↥S)) h
    simp only [Sylow.pointwise_smul_def] at this
    rw [smul_coe, MulAut.conjNormal_val]
    exact this

theorem smul_self_of_mem [Fact p.Prime] (V : Sylow p ↥S) (v : ↥S) (hv : v ∈ (V : Subgroup ↥S)) :
    (v : H) • V = V :=
  (coe_smul_eq_iff v V).2 (Subgroup.le_normalizer hv)

theorem conj_mem_of_smul_eq (ψ : H) (V : Sylow p ↥S) (h : ψ • V = V) (v : ↥S)
    (hv : v ∈ (V : Subgroup ↥S)) : ((MulAut.conjNormal ψ : MulAut ↥S) v) ∈ (V : Subgroup ↥S) := by
  have h1 := congrArg (fun W : Sylow p ↥S => (W : Subgroup ↥S)) h
  simp only [smul_coe] at h1
  rw [← h1]
  exact Subgroup.smul_mem_pointwise_smul v _ _ hv


theorem numeric_aux (j : ℕ) (hj : j ≤ 10) (hmod : 2 ^ j ≡ 1024 [MOD 5])
    (h25 : 25 ∣ 2 ^ j + 1) : 2 ^ j + 1 = 1025 := by
  interval_cases j <;> first | rfl | (exfalso; revert hmod h25; decide)

omit [S.Normal] in
theorem card_sylow_two [Finite H] (hSz : SzSylow ↥S) (V : Sylow 2 ↥S) :
    Nat.card (V : Subgroup ↥S) = 1024 := by
  have h2 : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  rw [Sylow.card_eq_multiplicity V, hSz.card, factorization_two]
  norm_num

omit [S.Normal] in
theorem card_sylow_two_subgroups (hSz : SzSylow ↥S) :
    Nat.card (Sylow 2 ↥S) = 1025 := hSz.card_sylow

omit [S.Normal] in
theorem card_normalizer_sylow_two (hSz : SzSylow ↥S) (V : Sylow 2 ↥S) :
    Nat.card (Subgroup.normalizer (V : Set ↥S)) = 31744 := by
  have h2 : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hfin : Finite ↥S := Nat.finite_of_card_ne_zero (by rw [hSz.card]; norm_num)
  have h0 := Sylow.card_eq_index_normalizer V
  have h1 := Subgroup.card_mul_index (Subgroup.normalizer (V : Set ↥S))
  rw [← h0, hSz.card_sylow, hSz.card] at h1
  omega

theorem free_of_pgroup [Finite H] (hSz : SzSylow ↥S) {T P' : Subgroup H} (hTS : T ≤ S)
    (hP'p : IsPGroup 5 P') (hTP' : T ≤ P') :
    ∀ t ∈ T, ∀ V : Sylow 2 ↥S, t • V = V → t = 1 := by
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h2 : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  intro t ht V hV
  have hts : t ∈ S := hTS ht
  have h1 : ((⟨t, hts⟩ : ↥S) : H) • V = V := hV
  have h2' := (coe_smul_eq_iff (⟨t, hts⟩ : ↥S) V).1 h1
  obtain ⟨k, hk⟩ := hP'p ⟨t, hTP' ht⟩
  have hk' : t ^ (5 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hdvd1 : orderOf t ∣ 5 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hdvd2 : orderOf t ∣ 31744 := by
    have := orderOf_dvd_natCard (⟨⟨t, hts⟩, h2'⟩ : ↥(Subgroup.normalizer (V : Set ↥S)))
    rw [card_normalizer_sylow_two hSz V] at this
    have e : orderOf (⟨⟨t, hts⟩, h2'⟩ : ↥(Subgroup.normalizer (V : Set ↥S))) = orderOf t := by
      rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
    rwa [e] at this
  have hcop : Nat.Coprime (5 ^ k) 31744 := Nat.Coprime.pow_left k (by norm_num)
  have h3 : orderOf t ∣ 1 := by
    have := Nat.dvd_gcd hdvd1 hdvd2
    rwa [hcop.gcd_eq_one] at this
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)

theorem exists_fixed [Finite H] (hSz : SzSylow ↥S) {P' : Subgroup H} (hP'card : 125 ∣ Nat.card P') :
    ∃ ψ ∈ P', ψ ≠ 1 ∧ ∃ V : Sylow 2 ↥S, ψ • V = V := by
  by_contra hcon
  push Not at hcon
  have hfree : ∀ q : ↥P', ∀ V : Sylow 2 ↥S, q • V = V → q = 1 := by
    intro q V hqV
    by_contra hq1
    exact hcon q q.2 (fun h => hq1 (Subtype.ext h)) V hqV
  have h1 := card_dvd_of_free (Q := ↥P') (X := Sylow 2 ↥S) hfree
  rw [card_sylow_two_subgroups hSz] at h1
  have h3 := Nat.dvd_trans hP'card h1
  omega

theorem fixed_all [Finite H] (hSz : SzSylow ↥S) {T : Subgroup H}
    (hTcard : Nat.card T = 25) (hfreeT : ∀ t ∈ T, ∀ V : Sylow 2 ↥S, t • V = V → t = 1)
    {ψ : H} (hψcomm : ∀ t ∈ T, ψ * t = t * ψ) (hord : ∃ k : ℕ, ψ ^ (5 ^ k) = 1)
    {V : Sylow 2 ↥S} (hψV : ψ • V = V) : ∀ W : Sylow 2 ↥S, ψ • W = W := by
  classical
  have h2 : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hΩcard := card_sylow_two_subgroups hSz
  have hVcard := card_sylow_two hSz
  obtain ⟨t₀, ht₀, ht₀1⟩ : ∃ t₀ ∈ T, t₀ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : T = ⊥ := (Subgroup.eq_bot_iff_forall T).2 hcon
    rw [hbot, Subgroup.card_bot] at hTcard
    omega
  set V₂ : Sylow 2 ↥S := t₀ • V with hV₂
  have hV₂V : V₂ ≠ V := fun h => ht₀1 (hfreeT t₀ ht₀ V h)
  have hψV₂ : ψ • V₂ = V₂ := by
    show ψ • (t₀ • V) = t₀ • V
    rw [← mul_smul, hψcomm t₀ ht₀, mul_smul, hψV]
  set U : Subgroup H := (V : Subgroup ↥S).map S.subtype with hU
  have hUcard : Nat.card U = 1024 := by
    rw [hU, Subgroup.card_map_of_injective S.subtype_injective, hVcard V]
  have hmemU : ∀ u ∈ U, ∃ v : ↥S, v ∈ (V : Subgroup ↥S) ∧ (v : H) = u := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨v, hv, rfl⟩
  have hU1 : ∀ u ∈ U, u • V = V := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := hmemU u hu
    exact smul_self_of_mem V v hv
  have hfreeU : ∀ u ∈ U, ∀ W : Sylow 2 ↥S, W ≠ V → u • W = W → u = 1 := by
    intro u hu W hWV hW
    obtain ⟨v, hv, rfl⟩ := hmemU u hu
    have h1 := (coe_smul_eq_iff v W).1 hW
    have h2' : v ∈ (V : Subgroup ↥S) ⊓ Subgroup.normalizer (W : Set ↥S) := ⟨hv, h1⟩
    rw [IsPGroup.inf_normalizer_sylow V.2 W, hSz.ti V W (Ne.symm hWV)] at h2'
    have : v = 1 := Subgroup.mem_bot.1 h2'
    rw [this]
    rfl
  have hconjU : ∀ g : H, g • V = V → ∀ u ∈ U, g * u * g⁻¹ ∈ U := by
    intro g hg u hu
    obtain ⟨v, hv, rfl⟩ := hmemU u hu
    have := conj_mem_of_smul_eq g V hg v hv
    refine ⟨_, this, ?_⟩
    simp [MulAut.conjNormal_apply]
  have hψU : ∀ u ∈ U, ψ * u * ψ⁻¹ ∈ U := hconjU ψ hψV
  have hfix := card_fixed_eq_of_regular (G := H) (Ω := Sylow 2 ↥S) U V hU1 hfreeU
    (by rw [hUcard, hΩcard]) ψ hψU hψV V₂ hV₂V hψV₂
  have hψN : ψ ∈ Subgroup.normalizer (U : Set H) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => hψU x hx
    · intro hx
      have hψ'V : ψ⁻¹ • V = V := by rw [inv_smul_eq_iff]; exact hψV.symm
      simpa [mul_assoc] using hconjU ψ⁻¹ hψ'V _ hx
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hmod := card_centralizer_modEq 5 U ψ hψN hord
  rw [hUcard] at hmod
  let Csub : Subgroup U :=
    { carrier := {u | ψ * (u : H) * ψ⁻¹ = (u : H)}
      mul_mem' := fun {a b} ha hb => by
        have ha' : ψ * (a : H) * ψ⁻¹ = (a : H) := ha
        have hb' : ψ * (b : H) * ψ⁻¹ = (b : H) := hb
        show ψ * ((a : H) * (b : H)) * ψ⁻¹ = (a : H) * (b : H)
        calc ψ * ((a : H) * (b : H)) * ψ⁻¹ = (ψ * (a : H) * ψ⁻¹) * (ψ * (b : H) * ψ⁻¹) := by
              group
          _ = (a : H) * (b : H) := by rw [ha', hb']
      one_mem' := by
        show ψ * (1 : H) * ψ⁻¹ = 1
        simp
      inv_mem' := fun {a} ha => by
        have ha' : ψ * (a : H) * ψ⁻¹ = (a : H) := ha
        show ψ * (a : H)⁻¹ * ψ⁻¹ = (a : H)⁻¹
        calc ψ * (a : H)⁻¹ * ψ⁻¹ = (ψ * (a : H) * ψ⁻¹)⁻¹ := by group
          _ = (a : H)⁻¹ := by rw [ha'] }
  have hCdvd : Nat.card {u : U // ψ * u * ψ⁻¹ = u} ∣ 2 ^ 10 := by
    have e : Nat.card {u : U // ψ * u * ψ⁻¹ = u} = Nat.card Csub :=
      Nat.card_congr (Equiv.subtypeEquivRight fun u => Iff.rfl)
    rw [e]
    have := Subgroup.card_subgroup_dvd_card Csub
    rw [hUcard] at this
    simpa using this
  obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 2)).1 hCdvd
  set F : Set (Sylow 2 ↥S) := {W | ψ • W = W} with hF
  have hFcard : Nat.card F = Nat.card {u : U // ψ * u * ψ⁻¹ = u} + 1 := hfix
  have hY : ∀ q : ↥T, ∀ y ∈ F, q • y ∈ F := by
    intro q y hy
    show ψ • ((q : H) • y) = (q : H) • y
    have hy' : ψ • y = y := hy
    rw [← mul_smul, hψcomm q q.2, mul_smul, hy']
  have h25 : Nat.card T ∣ Nat.card F :=
    card_dvd_of_free_invariant (Q := ↥T) (X := Sylow 2 ↥S)
      (fun q V hqV => Subtype.ext (hfreeT q q.2 V hqV)) F hY
  rw [hTcard, hFcard, hjeq] at h25
  have hFall : Nat.card F = Nat.card (Sylow 2 ↥S) := by
    rw [hFcard, hjeq, hΩcard]
    rw [hjeq] at hmod
    exact numeric_aux j hj hmod h25
  by_contra hne
  push Not at hne
  obtain ⟨W, hW⟩ := hne
  have hinj : Function.Injective (fun x : F => (⟨x.1, fun h => hW (by
      have := x.2
      rw [h] at this
      exact this)⟩ : {ω : Sylow 2 ↥S // ω ≠ W})) := by
    intro x y hxy
    have h1 := congrArg Subtype.val hxy
    exact Subtype.ext h1
  have h1 := Nat.card_le_card_of_injective _ hinj
  have h2' := card_ne_add_one W
  omega

theorem faithful [Finite H] (hSz : SzSylow ↥S) (hsimple : IsSimpleGroup ↥S)
    (hC : Subgroup.centralizer (S : Set H) = ⊥) {ψ : H} (hall : ∀ W : Sylow 2 ↥S, ψ • W = W) :
    ψ = 1 := by
  have h2 : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  obtain ⟨V⟩ : Nonempty (Sylow 2 ↥S) := inferInstance
  let N : Subgroup H := (MulAction.toPermHom H (Sylow 2 ↥S)).ker
  have hNn : N.Normal := MonoidHom.normal_ker _
  have hψN' : ψ ∈ N := by
    rw [MonoidHom.mem_ker]
    exact Equiv.ext fun W => hall W
  have hNS : N ⊓ S = ⊥ := by
    have hK : (N.subgroupOf S).Normal := Subgroup.Normal.subgroupOf hNn S
    have := hsimple
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf S) with hbot | htop
    · rw [eq_bot_iff]
      intro x hx
      have h1 : (⟨x, hx.2⟩ : ↥S) ∈ N.subgroupOf S := hx.1
      rw [hbot] at h1
      have h3 : (⟨x, hx.2⟩ : ↥S) = 1 := Subgroup.mem_bot.1 h1
      exact Subgroup.mem_bot.2 (congrArg Subtype.val h3)
    · exfalso
      have hVn : (V : Subgroup ↥S).Normal := by
        refine ⟨fun x hx g => ?_⟩
        have hgN : g ∈ N.subgroupOf S := htop ▸ Subgroup.mem_top g
        have hgN' : (g : H) ∈ N := hgN
        rw [MonoidHom.mem_ker] at hgN'
        have h1 := (coe_smul_eq_iff g V).1 (by
          have := congrArg (fun π : Equiv.Perm (Sylow 2 ↥S) => π V) hgN'
          simpa using this)
        have h2' := Subgroup.mem_normalizer_iff.1 h1 x
        exact (h2'.1 hx)
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (V : Subgroup ↥S) with h | h
      · have := card_sylow_two hSz V
        rw [h, Subgroup.card_bot] at this
        omega
      · have := card_sylow_two hSz V
        rw [h, Subgroup.card_top, hSz.card] at this
        omega
  have hNC : N ≤ Subgroup.centralizer (S : Set H) := by
    intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have h1 : n * s * n⁻¹ * s⁻¹ ∈ N := by
      have : s * n⁻¹ * s⁻¹ ∈ N := hNn.conj_mem _ (N.inv_mem hn) s
      have h3 := N.mul_mem hn this
      simpa [mul_assoc] using h3
    have h2' : n * s * n⁻¹ * s⁻¹ ∈ S := by
      have h4 : n * s * n⁻¹ ∈ S := Subgroup.Normal.conj_mem ‹S.Normal› s hs n
      exact S.mul_mem h4 (S.inv_mem hs)
    have h3 : n * s * n⁻¹ * s⁻¹ ∈ N ⊓ S := ⟨h1, h2'⟩
    rw [hNS, Subgroup.mem_bot] at h3
    have h5 : n * s * n⁻¹ = s := mul_inv_eq_one.1 h3
    calc s * n = n * s * n⁻¹ * n := by rw [h5]
      _ = n * s := by group
  have h6 : ψ ∈ Subgroup.centralizer (S : Set H) := hNC hψN'
  rw [hC] at h6
  exact Subgroup.mem_bot.1 h6

theorem sz_core [Finite H] (hSz : SzSylow ↥S) (hsimple : IsSimpleGroup ↥S)
    (hC : Subgroup.centralizer (S : Set H) = ⊥) {T P' : Subgroup H} (hTS : T ≤ S)
    (hTcard : Nat.card T = 25) (hP'p : IsPGroup 5 P') (hTP' : T ≤ P')
    (hP'card : 125 ∣ Nat.card P') (hcomm : ∀ x ∈ P', ∀ t ∈ T, x * t = t * x) : False := by
  have hfreeT := free_of_pgroup hSz hTS hP'p hTP'
  obtain ⟨ψ, hψP, hψ1, V, hψV⟩ := exists_fixed hSz hP'card
  have hord : ∃ k : ℕ, ψ ^ (5 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := hP'p ⟨ψ, hψP⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hall := fixed_all hSz hTcard hfreeT (fun t ht => hcomm ψ hψP t ht) hord hψV
  exact hψ1 (faithful hSz hsimple hC hall)

end ActionPart


end CFSG.RankThree.PartOne.K159.SzAbs
