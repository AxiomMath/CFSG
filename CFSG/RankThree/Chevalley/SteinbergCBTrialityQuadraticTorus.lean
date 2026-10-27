module

public import CFSG.RankThree.Chevalley.SteinbergCBTrialityQuadraticDescent

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def trialityConjImage
    (K : Type) [Field K] {K₂ : Type} [Field K₂] [Algebra K K₂]
    (σ : K →+* K) (g : ModGL TwistTag.D4.tag K₂) : Subgroup (ModGL TwistTag.D4.tag K₂) :=
  (graphFixedRootGroup TwistTag.D4 K σ).map
    ((MulAut.conj g).toMonoidHom.comp (baseChangeGL (algebraMap K K₂)))

section Torus

variable {τ : Tag} {L : Type} [Field L]

theorem units_map_entrywiseHom_of_mem_torusGroup
    {F : L →+* L} {n : ℕ} (hF : ∀ c, F c = c ^ n)
    {x : ModGL τ L} (hx : x ∈ torusGroup τ L) : Units.map (entrywiseHom F) x = x ^ n := by
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx
  rw [entrywise_frob_rootDiagUnit F hF, rootDiagUnit_pow]

theorem commute_of_mem_torusGroup
    {x y : ModGL τ L} (hx : x ∈ torusGroup τ L)
    (hy : y ∈ torusGroup τ L) : x * y = y * x := by
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx
  obtain ⟨l', rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hy
  rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]

end Torus

theorem twistedEntrywise_trialityOpposition_of_mem_torusGroup
    {L : Type} [Field L] {F : L →+* L}
    {n : ℕ} (hF : ∀ c, F c = c ^ n) {x : ModGL TwistTag.D4.tag L}
    (hx : x ∈ torusGroup TwistTag.D4.tag L) :
    twistedEntrywise (trialityOpposition L) F x = (x ^ n)⁻¹ := by
  rw [twistedEntrywise_apply, units_map_entrywiseHom_of_mem_torusGroup hF hx,
    trialityOpposition_conj_torus (pow_mem hx n)]

theorem graphFixedRootTorus_le_torusGroup
    {t : TwistTag} {L : Type} [Field L] (σ : L →+* L) :
    graphFixedRootTorus t L σ ≤ torusGroup t.tag L :=
  fun _ hx => (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx).1).1

theorem not_dvd_of_triality_index {q I p : ℕ} (hq : 1 ≤ q) (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ∣ q + 1)
    (h : (q ^ 3 + 1) * (q + 1) * I = q ^ 12 * (q ^ 2 - 1) * (q ^ 6 - 1) * (q ^ 8 + q ^ 4 + 1)) :
    ¬ p ∣ I := by
  have hZ : ((q : ℤ) ^ 3 + 1) * ((q : ℤ) + 1) * I =
      (q : ℤ) ^ 12 * ((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 6 - 1) * ((q : ℤ) ^ 8 + (q : ℤ) ^ 4 + 1) := by
    have h6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ hq
    have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
    have h' := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast [Nat.cast_sub h6, Nat.cast_sub h2] at h'
    exact h'
  have hI : (I : ℤ) = (q : ℤ) ^ 12 * ((q : ℤ) - 1) * ((q : ℤ) ^ 3 - 1) *
      ((q : ℤ) ^ 8 + (q : ℤ) ^ 4 + 1) := by
    have hne : ((q : ℤ) ^ 3 + 1) * ((q : ℤ) + 1) ≠ 0 := by positivity
    apply mul_left_cancel₀ hne
    rw [hZ]
    ring
  intro hdvd
  have hI0 : (I : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff I p).2 hdvd
  have hqp : (q : ZMod p) = -1 := by
    have h1 := (ZMod.natCast_eq_zero_iff (q + 1) p).2 hpq
    push_cast at h1
    linear_combination h1
  have h12 : ((12 : ℕ) : ZMod p) = 0 := by
    have h' := congrArg (Int.cast : ℤ → ZMod p) hI
    push_cast at h'
    rw [hqp, hI0] at h'
    rw [h']
    norm_num
  have hp12 := (ZMod.natCast_eq_zero_iff 12 p).1 h12
  have := Nat.le_of_dvd (by norm_num) hp12
  interval_cases p <;> first | (norm_num at hp; done) | norm_num at hp12

theorem dvd_of_int_eq_mul {a b : ℕ} (c : ℤ) (h : (b : ℤ) = a * c) : a ∣ b :=
  Int.natCast_dvd_natCast.1 ⟨c, h⟩

theorem pow_three_add_one_dvd {q : ℕ} (hq : 1 ≤ q) : q ^ 3 + 1 ∣ q ^ 6 - 1 :=
  dvd_of_int_eq_mul ((q : ℤ) ^ 3 - 1) (by
    push_cast [Nat.cast_sub (Nat.one_le_pow 6 q hq)]
    ring)

theorem add_one_dvd_sq_sub_one {q : ℕ} (hq : 1 ≤ q) : q + 1 ∣ q ^ 2 - 1 :=
  dvd_of_int_eq_mul ((q : ℤ) - 1) (by
    push_cast [Nat.cast_sub (Nat.one_le_pow 2 q hq)]
    ring)

theorem sq_sub_one_dvd_pow_six {q : ℕ} (hq : 1 ≤ q) : q ^ 2 - 1 ∣ q ^ 6 - 1 := by
  refine Int.natCast_dvd_natCast.1 ⟨(q : ℤ) ^ 4 + (q : ℤ) ^ 2 + 1, ?_⟩
  push_cast [Nat.cast_sub (Nat.one_le_pow 6 q hq), Nat.cast_sub (Nat.one_le_pow 2 q hq)]
  ring

theorem natCard_multiplicative_zmod (n : ℕ) : Nat.card (Multiplicative (ZMod n)) = n := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem nonempty_rootsOfUnity_mulEquiv {F : Type} [Field F] [Finite F] {n : ℕ} [NeZero n]
    (hn : n ∣ Nat.card F - 1) : Nonempty (rootsOfUnity n F ≃* Multiplicative (ZMod n)) :=
  ⟨mulEquivOfCyclicCardEq (by
    rw [card_rootsOfUnity_of_dvd_card_sub_one hn, natCard_multiplicative_zmod])⟩

theorem mem_torus_inf_trialityConjImage_iff
    {L : Type} [Field L] {C₂ H₂ Γ : Subgroup
    (ModGL TwistTag.D4.tag L)} {τ : L →+* L} {n : ℕ} (hτ : ∀ c, τ c = c ^ n)
    (hΓ : Γ = C₂ ⊓ (twistedEntrywise (trialityOpposition L) τ).eqLocus (MonoidHom.id _))
    (hHC : H₂ ≤ C₂) (hHT : H₂ ≤ torusGroup TwistTag.D4.tag L) (x : ModGL TwistTag.D4.tag L) :
    x ∈ H₂ ⊓ Γ ↔ x ∈ H₂ ∧ x ^ (n + 1) = 1 := by
  rw [Subgroup.mem_inf, hΓ, Subgroup.mem_inf]
  refine and_congr_right fun hx => ?_
  have hF := twistedEntrywise_trialityOpposition_of_mem_torusGroup hτ (hHT hx)
  constructor
  · rintro ⟨-, hfix⟩
    have hfix' : twistedEntrywise (trialityOpposition L) τ x = x := hfix
    rw [hF] at hfix'
    calc x ^ (n + 1) = x ^ n * x := pow_succ x n
      _ = x ^ n * (x ^ n)⁻¹ := by rw [hfix']
      _ = 1 := mul_inv_cancel _
  · intro h1
    refine ⟨hHC hx, ?_⟩
    change twistedEntrywise (trialityOpposition L) τ x = x
    rw [hF]
    rw [pow_succ] at h1
    exact inv_eq_of_mul_eq_one_right h1

theorem triality_qplus_quadratic_realization_and_toral_Sylow
    (ℓ f : ℕ) (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) (K K₂ : Type) [Field K] [Field K₂] [Algebra K K₂]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (hK₂ : Nat.card K₂ = (ℓ ^ f) ^ 6)
    (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (σ₂ : K₂ ≃+* K₂) (hσ₂ : ∀ c, σ₂ c = c ^ ((ℓ ^ f) ^ 4))
    (τ : K₂ →+* K₂) (hτ : ∀ c, τ c = c ^ ((ℓ ^ f) ^ 3)) :
    graphFixedRootGroup TwistTag.D4 K₂ σ₂.toRingHom ⊓
        (Units.map (entrywiseHom τ)).eqLocus (MonoidHom.id _) =
      (graphFixedRootGroup TwistTag.D4 K σ).map (baseChangeGL (algebraMap K K₂)) ∧
    trialityOpposition K₂ ∈ graphFixedRootGroup TwistTag.D4 K₂ σ₂.toRingHom ∧
    (∃ g ∈ graphFixedRootGroup TwistTag.D4 K₂ σ₂.toRingHom,
      trialityOpposition K₂ = g * (Units.map (entrywiseHom τ) g)⁻¹) ∧
    ∀ g ∈ graphFixedRootGroup TwistTag.D4 K₂ σ₂.toRingHom,
      trialityOpposition K₂ = g * (Units.map (entrywiseHom τ) g)⁻¹ →
      (∀ y, twistedEntrywise (trialityOpposition K₂) τ
        (twistedEntrywise (trialityOpposition K₂) τ y) = y) ∧
      trialityConjImage K σ g = graphFixedRootGroup TwistTag.D4 K₂ σ₂.toRingHom ⊓
        (twistedEntrywise (trialityOpposition K₂) τ).eqLocus (MonoidHom.id _) ∧
      (∀ x, x ∈ graphFixedRootTorus TwistTag.D4 K₂ σ₂.toRingHom ⊓ trialityConjImage K σ g ↔
        ∃ (a : K₂ˣ) (b : (trialityFixedField K₂ σ₂.toRingHom)ˣ),
          a ^ ((ℓ ^ f) ^ 3 + 1) = 1 ∧ b ^ (ℓ ^ f + 1) = 1 ∧
            x = trialityOuterTorus K₂ σ₂ a * trialityMiddleTorus K₂ σ₂ b) ∧
      (∀ (a a' : K₂ˣ) (b b' : (trialityFixedField K₂ σ₂.toRingHom)ˣ),
        trialityOuterTorus K₂ σ₂ a * trialityMiddleTorus K₂ σ₂ b =
          trialityOuterTorus K₂ σ₂ a' * trialityMiddleTorus K₂ σ₂ b' → a = a' ∧ b = b') ∧
      Nonempty ((graphFixedRootTorus TwistTag.D4 K₂ σ₂.toRingHom ⊓ trialityConjImage K σ g :
          Subgroup (ModGL TwistTag.D4.tag K₂)) ≃*
        Multiplicative (ZMod ((ℓ ^ f) ^ 3 + 1)) × Multiplicative (ZMod (ℓ ^ f + 1))) ∧
      ∀ p : ℕ, p.Prime → 3 < p → p ∣ ℓ ^ f + 1 →
        (∃ S : Sylow p (trialityConjImage K σ g),
          (S : Subgroup (trialityConjImage K σ g)) ≤
            (graphFixedRootTorus TwistTag.D4 K₂ σ₂.toRingHom ⊓
              trialityConjImage K σ g).subgroupOf (trialityConjImage K σ g)) ∧
        ∃ V : Subgroup (ModGL TwistTag.D4.tag K₂),
          (∀ h, h ∈ V ↔ h ∈ graphFixedRootTorus TwistTag.D4 K₂ σ₂.toRingHom ∧ h ^ p = 1) ∧
          V ≤ graphFixedRootTorus TwistTag.D4 K₂ σ₂.toRingHom ⊓ trialityConjImage K σ g ∧
          Nat.card V = p ^ 2 ∧ (∀ x ∈ V, ∀ y ∈ V, x * y = y * x) ∧ ∀ x ∈ V, x ^ p = 1 := by
  classical
  set H₂ := graphFixedRootTorus TwistTag.D4 K₂ σ₂.toRingHom with hH₂def
  set C₂ := graphFixedRootGroup TwistTag.D4 K₂ σ₂.toRingHom with hC₂def
  set k₂ := trialityFixedField K₂ σ₂.toRingHom
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
  have : Finite K₂ := Nat.finite_of_card_ne_zero (by
    rw [hK₂]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have hq6 : ∀ c : K₂, c ^ ((ℓ ^ f) ^ 6) = c := pow_q_six_eq hK₂ hℓ
  have hσ₂3 : σ₂ ^ 3 = 1 := RingEquiv.ext fun c => by
    change σ₂ (σ₂ (σ₂ c)) = c
    rw [hσ₂, hσ₂, hσ₂, ← pow_mul, ← pow_mul,
      show (ℓ ^ f) ^ 4 * ((ℓ ^ f) ^ 4 * (ℓ ^ f) ^ 4) = (ℓ ^ f) ^ 6 * (ℓ ^ f) ^ 6 by ring, pow_mul,
      hq6, hq6]
  obtain ⟨-, ⟨e, he⟩, -, hL2, -, -, -, -, -⟩ :=
    triality_all_characteristic_faithful_torus_coordinates K₂ σ₂ hσ₂3
  have hk₂ : Nat.card (trialityFixedField K₂ σ₂.toRingHom) = (ℓ ^ f) ^ 2 := by
    have hK₂' : Nat.card K₂ = (ℓ ^ (2 * f)) ^ 3 := by
      rw [hK₂]
      ring
    have hσ₂' : ∀ c, σ₂.toRingHom c = c ^ ((ℓ ^ (2 * f)) ^ 2) := fun c => by
      change σ₂ c = _
      rw [hσ₂]
      congr 1
      ring
    have h := card_orbitField_D4_orientation hℓ (by omega : 1 ≤ 2 * f) hK₂' (Or.inr rfl) hσ₂'
      ⟨1, by decide⟩
    rw [hL2, show (TwistTag.D4.orbit ⟨1, by decide⟩).card = 1 by decide, pow_one] at h
    rw [h]
    ring
  have hCτ := graphFixedRootGroup_inf_eqLocus_eq hℓ hf K K₂ hK hK₂ σ hσ σ₂.toRingHom hσ₂ τ hτ
  obtain ⟨g₀, hg₀, hz₀⟩ :=
    exists_eq_mul_inv_entrywise_trialityOpposition hℓ hf K₂ hK₂ σ₂.toRingHom hσ₂ τ hτ
  have hord := (triality_both_orientations_exact_finite_order ℓ f hℓ hf K hK 1 (Or.inl rfl) σ
    fun c => by rw [hσ, pow_one]).1
  generalize hqdef : ℓ ^ f = q at hK hK₂ hσ hσ₂ hτ hk₂ hord hq1 hq6 ⊢
  refine ⟨hCτ, trialityOpposition_mem_graphFixedRootGroup _, ⟨g₀, hg₀, hz₀⟩, fun g hg hzg => ?_⟩
  have hττ : ∀ c, τ (τ c) = c := fun c => by
    rw [hτ, hτ, ← pow_mul, show q ^ 3 * q ^ 3 = q ^ 6 by ring, hq6]
  have hΓ : trialityConjImage K σ g =
      C₂ ⊓ (twistedEntrywise (trialityOpposition K₂) τ).eqLocus (MonoidHom.id _) := by
    rw [trialityConjImage, ← Subgroup.map_map]
    exact map_conj_eq_inf_eqLocus hCτ hg hzg
  have hT := mem_torus_inf_trialityConjImage_iff hτ hΓ (graphFixedRootTorus_le _ _ _)
    (graphFixedRootTorus_le_torusGroup _)
  have hmemH : ∀ x, x ∈ H₂ ↔ ∃ (a : K₂ˣ) (b : k₂ˣ),
      x = trialityOuterTorus K₂ σ₂ a * trialityMiddleTorus K₂ σ₂ b := by
    intro x
    constructor
    · intro hx
      refine ⟨(e.symm ⟨x, hx⟩).1, (e.symm ⟨x, hx⟩).2, ?_⟩
      rw [← he, Prod.mk.eta, MulEquiv.apply_symm_apply]
    · rintro ⟨a, b, rfl⟩
      rw [← he]
      exact (e (a, b)).2
  have hpow : ∀ (a : K₂ˣ) (b : k₂ˣ) (n : ℕ),
      (trialityOuterTorus K₂ σ₂ a * trialityMiddleTorus K₂ σ₂ b) ^ n =
        trialityOuterTorus K₂ σ₂ (a ^ n) * trialityMiddleTorus K₂ σ₂ (b ^ n) := by
    intro a b n
    rw [← he, ← he, ← Subgroup.coe_pow, ← map_pow, Prod.pow_mk]
  have hinj : ∀ (a a' : K₂ˣ) (b b' : k₂ˣ),
      trialityOuterTorus K₂ σ₂ a * trialityMiddleTorus K₂ σ₂ b =
        trialityOuterTorus K₂ σ₂ a' * trialityMiddleTorus K₂ σ₂ b' → a = a' ∧ b = b' := by
    intro a a' b b' h
    rw [← he, ← he] at h
    exact Prod.ext_iff.1 (e.injective (Subtype.ext h))
  have h11 : trialityOuterTorus K₂ σ₂ 1 * trialityMiddleTorus K₂ σ₂ 1 = 1 := by
    rw [← he, ← Prod.one_eq_mk, map_one]
    rfl
  have hb : ∀ b : k₂ˣ, b ^ (q ^ 3 + 1) = b ^ (q + 1) := by
    intro b
    have : Finite k₂ := Subtype.finite
    have : Fintype k₂ := Fintype.ofFinite k₂
    have hbq : b ^ (q ^ 2) = b := Units.ext (by
      rw [Units.val_pow_eq_pow_val, ← hk₂, Nat.card_eq_fintype_card, FiniteField.pow_card])
    rw [show q ^ 3 + 1 = q ^ 2 * q + 1 by ring, pow_succ, pow_mul, hbq, pow_succ]
  have hTc : ∀ x, x ∈ H₂ ⊓ trialityConjImage K σ g ↔ ∃ (a : K₂ˣ) (b : k₂ˣ),
      a ^ (q ^ 3 + 1) = 1 ∧ b ^ (q + 1) = 1 ∧
        x = trialityOuterTorus K₂ σ₂ a * trialityMiddleTorus K₂ σ₂ b := by
    intro x
    rw [hT]
    constructor
    · rintro ⟨hx, h1⟩
      obtain ⟨a, b, rfl⟩ := (hmemH x).1 hx
      rw [hpow] at h1
      obtain ⟨ha, hb'⟩ := hinj _ _ _ _ (h1.trans h11.symm)
      exact ⟨a, b, ha, by rw [← hb b]; exact hb', rfl⟩
    · rintro ⟨a, b, ha, hb', rfl⟩
      refine ⟨(hmemH _).2 ⟨a, b, rfl⟩, ?_⟩
      rw [hpow, ha, hb b, hb', h11]
  set ψ : K₂ˣ × k₂ˣ →* ModGL TwistTag.D4.tag K₂ := H₂.subtype.comp e.toMonoidHom with hψ
  have hψ_apply : ∀ (a : K₂ˣ) (b : k₂ˣ),
      ψ (a, b) = trialityOuterTorus K₂ σ₂ a * trialityMiddleTorus K₂ σ₂ b := fun a b => he a b
  have hψinj : Function.Injective ψ := Subtype.val_injective.comp e.injective
  have hprodinj : ∀ m n : ℕ, Function.Injective
      ((rootsOfUnity m K₂).subtype.prodMap (rootsOfUnity n k₂).subtype) := fun m n => by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  set φT := ψ.comp ((rootsOfUnity (q ^ 3 + 1) K₂).subtype.prodMap
    (rootsOfUnity (q + 1) k₂).subtype) with hφT
  have hφTinj : Function.Injective φT := hψinj.comp (hprodinj _ _)
  have hφTrange : φT.range = H₂ ⊓ trialityConjImage K σ g := by
    ext x
    rw [hTc x, MonoidHom.mem_range]
    constructor
    · rintro ⟨⟨a, b⟩, rfl⟩
      exact ⟨a, b, (mem_rootsOfUnity _ _).1 a.2, (mem_rootsOfUnity _ _).1 b.2, hψ_apply _ _⟩
    · rintro ⟨a, b, ha, hb', rfl⟩
      exact ⟨(⟨a, (mem_rootsOfUnity _ _).2 ha⟩, ⟨b, (mem_rootsOfUnity _ _).2 hb'⟩),
        hψ_apply a b⟩
  set eT : rootsOfUnity (q ^ 3 + 1) K₂ × rootsOfUnity (q + 1) k₂ ≃*
      (H₂ ⊓ trialityConjImage K σ g : Subgroup (ModGL TwistTag.D4.tag K₂)) :=
    (MonoidHom.ofInjective hφTinj).trans (MulEquiv.subgroupCongr hφTrange)
  have : Finite k₂ := Subtype.finite
  have hq1' : 1 ≤ q := hq1
  have hK₂d : Nat.card K₂ - 1 = q ^ 6 - 1 := by rw [hK₂]
  have hk₂d : Nat.card k₂ - 1 = q ^ 2 - 1 := by rw [hk₂]
  have : NeZero (q ^ 3 + 1) := ⟨by omega⟩
  have : NeZero (q + 1) := ⟨by omega⟩
  have hd1 : q ^ 3 + 1 ∣ Nat.card K₂ - 1 := by rw [hK₂d]; exact pow_three_add_one_dvd hq1
  have hd2 : q + 1 ∣ Nat.card k₂ - 1 := by rw [hk₂d]; exact add_one_dvd_sq_sub_one hq1
  obtain ⟨e₁⟩ := nonempty_rootsOfUnity_mulEquiv hd1
  obtain ⟨e₂⟩ := nonempty_rootsOfUnity_mulEquiv hd2
  have hTcard : Nat.card (H₂ ⊓ trialityConjImage K σ g : Subgroup (ModGL TwistTag.D4.tag K₂)) =
      (q ^ 3 + 1) * (q + 1) := by
    rw [← Nat.card_congr eT.toEquiv, Nat.card_prod, card_rootsOfUnity_of_dvd_card_sub_one hd1,
      card_rootsOfUnity_of_dvd_card_sub_one hd2]
  refine ⟨fun y => twistedEntrywise_twistedEntrywise hττ hzg y, hΓ, hTc, hinj,
    ⟨eT.symm.trans (MulEquiv.prodCongr e₁ e₂)⟩, fun p hp hp3 hpq => ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  have hΓcard : Nat.card (trialityConjImage K σ g) =
      q ^ 12 * (q ^ 2 - 1) * (q ^ 6 - 1) * (q ^ 8 + q ^ 4 + 1) := by
    rw [trialityConjImage, Subgroup.card_map_of_injective
      ((MulAut.conj g).injective.comp (baseChangeGL_injective (τ := TwistTag.D4.tag) _)), hord]
  have : Finite (trialityConjImage K σ g) := Nat.finite_of_card_ne_zero (by
    rw [hΓcard]
    have h2 : 1 < q ^ 2 := Nat.one_lt_pow (by norm_num) (by
      have := hqdef ▸ (Nat.le_self_pow (by omega : f ≠ 0) ℓ)
      have h2ℓ := hℓ.two_le
      omega)
    have h6 : 1 < q ^ 6 := by
      calc 1 < q ^ 2 := h2
        _ ≤ q ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
    exact (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by positivity) (by omega)) (by omega))
      (by positivity)).ne')
  set T' := (H₂ ⊓ trialityConjImage K σ g).subgroupOf (trialityConjImage K σ g)
  have hT'card : Nat.card T' = (q ^ 3 + 1) * (q + 1) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, hTcard]
  have hidx := T'.card_mul_index
  rw [hT'card, hΓcard] at hidx
  have hndvd := not_dvd_of_triality_index hq1 hp hp3 hpq hidx
  refine ⟨exists_sylow_le_of_not_dvd_index hndvd, ?_⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hp1 : p ∣ q ^ 3 + 1 := hpq.trans (by
    simpa only [one_pow] using (by decide : Odd 3).nat_add_dvd_pow_add_pow q 1)
  have hpK₂ : p ∣ Nat.card K₂ - 1 := by
    rw [hK₂d]
    exact hpq.trans ((add_one_dvd_sq_sub_one hq1).trans (sq_sub_one_dvd_pow_six hq1))
  have hpk₂ : p ∣ Nat.card k₂ - 1 := by
    rw [hk₂d]
    exact hpq.trans (add_one_dvd_sq_sub_one hq1)
  set φV := ψ.comp ((rootsOfUnity p K₂).subtype.prodMap (rootsOfUnity p k₂).subtype) with hφV
  have hφVinj : Function.Injective φV := hψinj.comp (hprodinj _ _)
  have hV : ∀ h, h ∈ φV.range ↔ h ∈ H₂ ∧ h ^ p = 1 := by
    intro h
    rw [MonoidHom.mem_range]
    constructor
    · rintro ⟨⟨a, b⟩, rfl⟩
      refine ⟨(e _).2, ?_⟩
      have ha : a ^ p = 1 := Subtype.ext (by simpa using (mem_rootsOfUnity _ _).1 a.2)
      have hb' : b ^ p = 1 := Subtype.ext (by simpa using (mem_rootsOfUnity _ _).1 b.2)
      rw [← map_pow, Prod.pow_mk, ha, hb', ← Prod.one_eq_mk, map_one]
    · rintro ⟨hh, h1⟩
      set y := e.symm ⟨h, hh⟩
      have hy : ψ y = h := by
        change ((e (e.symm ⟨h, hh⟩) : H₂) : ModGL TwistTag.D4.tag K₂) = h
        rw [MulEquiv.apply_symm_apply]
      have hyp : y ^ p = 1 := hψinj (by rw [map_pow, hy, h1, map_one])
      refine ⟨(⟨y.1, (mem_rootsOfUnity _ _).2 (congrArg Prod.fst hyp)⟩,
        ⟨y.2, (mem_rootsOfUnity _ _).2 (congrArg Prod.snd hyp)⟩), ?_⟩
      exact hy
  refine ⟨φV.range, hV, fun h hh => ?_, ?_, fun x hx y hy => ?_, fun x hx => ((hV x).1 hx).2⟩
  · obtain ⟨hhH, hh1⟩ := (hV h).1 hh
    obtain ⟨m, hm⟩ := hp1
    refine (hT h).2 ⟨hhH, ?_⟩
    rw [hm, pow_mul, hh1, one_pow]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hφVinj).toEquiv, Nat.card_prod,
      card_rootsOfUnity_of_dvd_card_sub_one hpK₂, card_rootsOfUnity_of_dvd_card_sub_one hpk₂, sq]
  · exact commute_of_mem_torusGroup (graphFixedRootTorus_le_torusGroup _ ((hV x).1 hx).1)
      (graphFixedRootTorus_le_torusGroup _ ((hV y).1 hy).1)

end CFSG.RankThree.Chevalley
