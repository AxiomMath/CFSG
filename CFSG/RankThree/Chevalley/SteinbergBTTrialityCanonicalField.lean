module

public import CFSG.LieType.Chevalley.EvenTrialityCanonicalFieldCentralizer
public import CFSG.LieType.Chevalley.TrialityFullAmbientFixedGroup
public import CFSG.RankThree.Chevalley.SteinbergBTCanonicalFieldCommon

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley SteinbergBT

theorem triality_canonical_field_facts {ℓ d m : ℕ} (hℓ : ℓ.Prime) (hd : 1 ≤ d) (hm : 2 ≤ m)
    (hm3 : Nat.Coprime m 3) {K : Type} [Field K] [Finite K] (hK : Nat.card K = ℓ ^ (3 * d * m))
    {σ δ : K ≃+* K} (hσ : ∀ c, σ c = c ^ ℓ ^ (d * m)) (hδ : ∀ c, δ c = c ^ ℓ ^ (3 * d)) :
    σ ^ 3 = 1 ∧ orderOf δ = m ∧ δ ∈ Subgroup.zpowers (δ ^ 3) ∧
      Nat.card (fixSubfield δ) = ℓ ^ (3 * d) ∧ orderOf (fixSubfieldRestrict σ δ) = 3 := by
  have hpos : 1 ≤ 3 * d * m := Nat.one_le_iff_ne_zero.2 (by positivity)
  obtain ⟨fr, hfr, hord, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hℓ
      hpos hK
  have hσfr : σ = fr ^ (d * m) := RingEquiv.ext fun c => by
    rw [hσ, ringAut_pow_apply_of_frobenius hfr]
  have hδfr : δ = fr ^ (3 * d) := RingEquiv.ext fun c => by
    rw [hδ, ringAut_pow_apply_of_frobenius hfr]
  have hσ3 : σ ^ 3 = 1 := by
    rw [hσfr, ← pow_mul, show d * m * 3 = 3 * d * m by ring, ← hord, pow_orderOf_eq_one]
  have hσord : orderOf σ = 3 := by
    rw [hσfr, orderOf_pow_of_dvd (by positivity) (by rw [hord]; exact ⟨3, by ring⟩), hord,
      show 3 * d * m = 3 * (d * m) by ring, Nat.mul_div_cancel _ (by positivity)]
  have hδord : orderOf δ = m := by
    rw [hδfr, orderOf_pow_of_dvd (by omega) (by rw [hord]; exact Dvd.intro m rfl), hord,
      Nat.mul_div_cancel_left m (by omega)]
  have hδmem : δ ∈ Subgroup.zpowers (δ ^ 3) := by
    have hb := Nat.gcd_eq_gcd_ab 3 m
    rw [Nat.Coprime.gcd_eq_one hm3.symm] at hb
    push_cast at hb
    have hδm : δ ^ m = 1 := by
      rw [← hδord]
      exact pow_orderOf_eq_one δ
    refine Subgroup.mem_zpowers_iff.2 ⟨Nat.gcdA 3 m, ?_⟩
    calc (δ ^ 3) ^ Nat.gcdA 3 m = δ ^ ((3 : ℤ) * Nat.gcdA 3 m) := by
          rw [zpow_mul]
          norm_cast
      _ = δ ^ ((3 : ℤ) * Nat.gcdA 3 m + m * Nat.gcdB 3 m) := by
          rw [zpow_add, zpow_mul δ (m : ℤ), zpow_natCast, hδm, one_zpow, mul_one]
      _ = δ := by rw [← hb, zpow_one]
  obtain ⟨-, hk⟩ := card_fixSubfield hℓ hpos hK δ
  rw [hδord, Nat.mul_div_cancel _ (by omega)] at hk
  have h03 : fixSubfieldRestrict σ δ ^ 3 = 1 := fixSubfieldRestrict_pow_eq_one δ hσ3
  have h01 : fixSubfieldRestrict σ δ ≠ 1 := by
    intro h1
    have hfix : ∀ x, δ x = x → σ x = x := fun x hx => by
      have h2 := congrArg (fun ψ : fixSubfield δ ≃+* fixSubfield δ => (ψ ⟨x, hx⟩ : K)) h1
      exact h2
    have h3 := orderOf_dvd_of_mem_zpowers
      (CFSG.ComponentClassification.UnbalancedCatalog.mem_zpowers_of_fixed hfix)
    rw [hσord, hδord] at h3
    have h4 := Nat.gcd_eq_right h3
    rw [Nat.Coprime.gcd_eq_one hm3] at h4
    omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact ⟨hσ3, hδord, hδmem, hk, orderOf_eq_prime h03 h01⟩

theorem triality_canonical_field_full_centralizer_and_pointwise_kernel {ℓ d m : ℕ}
    (hℓ : ℓ.Prime) (hd : 1 ≤ d) (hm : 2 ≤ m) (hm3 : Nat.Coprime m 3) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = ℓ ^ (3 * d * m)) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ ℓ ^ (d * m)) (δ : K ≃+* K) (hδ : ∀ c, δ c = c ^ ℓ ^ (3 * d)) :
    orderOf (fieldActor (t := TwistTag.D4) σ δ) = m ∧
      (∀ c : K, c ∈ fixSubfield δ ↔ c ^ ℓ ^ (3 * d) = c) ∧
      Nat.card (fixSubfield δ) = ℓ ^ (3 * d) ∧
      (∀ c : fixSubfield δ, (fixSubfieldRestrict σ δ c : K) = σ c) ∧
      orderOf (fixSubfieldRestrict σ δ) = 3 ∧
      trialityFieldImage σ δ ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom ∧
      ((fieldActor σ δ).toMonoidHom.eqLocus (MonoidHom.id _)).map
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype = trialityFieldImage σ δ ∧
      IsSimpleGroup (trialityFieldImage σ δ) ∧
      (¬∀ a b : trialityFieldImage σ δ, a * b = b * a) ∧
      (∃ ι : ↥((trialityFieldImage σ δ).subgroupOf
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ≃* ↥(trialityFieldInner σ δ),
        ∀ j, (ι j : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) =
          MulAut.conj (j : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ∧
      (∀ β ∈ Subgroup.centralizer {fieldActor σ δ},
        ∃! gφ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom × (K ≃+* K),
          (gφ.1 : ModGL TwistTag.D4.tag K) ∈ trialityFieldImage σ δ ∧
            β = MulAut.conj gφ.1 * fieldActor σ gφ.2) ∧
      trialityFieldInner σ δ ≤ Subgroup.centralizer {fieldActor σ δ} ∧
      ((trialityFieldInner σ δ).subgroupOf (Subgroup.centralizer {fieldActor σ δ})).Normal ∧
      Subgroup.centralizer {fieldActor σ δ} ⊓
          Subgroup.centralizer (trialityFieldInner σ δ :
            Set (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) =
        Subgroup.zpowers (fieldActor σ δ) ∧
      Nat.card (Subgroup.zpowers (fieldActor (t := TwistTag.D4) σ δ)) = m := by
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hC
  obtain ⟨hσ3, hδord, hδmem, hk, hord⟩ := triality_canonical_field_facts hℓ hd hm hm3 hK hσ hδ
  have : Finite (fixSubfield δ) := Subtype.finite
  have hσ₀3 : ∀ c, fixSubfieldRestrict σ δ (fixSubfieldRestrict σ δ
      (fixSubfieldRestrict σ δ c)) = c := fun c => by
    have h := congrArg (fun ψ : fixSubfield δ ≃+* fixSubfield δ => ψ c)
      (pow_orderOf_eq_one (fixSubfieldRestrict σ δ))
    rw [hord] at h
    exact h
  have hσ3pt : ∀ c, σ (σ (σ c)) = c := fun c => congrArg (fun ψ : K ≃+* K => ψ c) hσ3
  have : CharP (fixSubfield δ) ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ
      (by omega : 1 ≤ 3 * d) hk
  have hcharK₀ : ringChar (fixSubfield δ) = ℓ := ringChar.eq (fixSubfield δ) ℓ
  have hpar₀ : ringChar (fixSubfield δ) = 2 ∨
      ∃ n, Odd n ∧ ∀ c, fixSubfieldRestrict σ δ c = c ^ n := by
    rcases hℓ.eq_two_or_odd' with h2 | hodd
    · exact Or.inl (hcharK₀.trans h2)
    · exact Or.inr ⟨ℓ ^ (d * m), hodd.pow, fun c => Subtype.ext (by
        rw [coe_fixSubfieldRestrict, hσ, SubmonoidClass.coe_pow])⟩
  have htw : twistedFixedGroup TwistTag.D4 K (σ * δ).toRingHom = trialityFieldImage σ δ :=
    twistedFixedGroup_D4_eq_map_baseChangeGL (ι := (fixSubfield δ).subtype)
      (σ := fixSubfieldRestrict σ δ) (ψ := σ * δ)
      (fun l hl => rootDiagUnit_mem_graphFixedRootGroup_triality _ hσ₀3 hpar₀ hl)
      (fun c => by
        change σ (δ c) = σ c
        rw [show δ (c : K) = c from c.2])
      (fun c hc => by
        have e : (σ * δ) ^ 3 = δ ^ 3 := by
          rw [(commute_ringEquiv_of_finite σ δ).mul_pow, hσ3, one_mul]
        have h3 : δ ^ 3 ∈ MulAction.stabilizer (K ≃+* K) c := by
          rw [MulAction.mem_stabilizer_iff, RingAut.smul_def, ← e, pow_three]
          exact hc
        have h1 := Subgroup.zpowers_le.2 h3 hδmem
        rw [MulAction.mem_stabilizer_iff, RingAut.smul_def] at h1
        exact ⟨⟨c, h1⟩, rfl⟩)
  have hJC : trialityFieldImage σ δ ≤ C :=
    map_baseChangeGL_graphFixedRootGroup_le (σ := (fixSubfieldRestrict σ δ).toRingHom)
      (Fr := σ.toRingHom) (ι := (fixSubfield δ).subtype) (fixSubfieldRestrict σ δ).surjective
      fun _ => rfl
  have hCadj : C ≤ adjointGroup TwistTag.D4.tag K := fun g hg =>
    twistedFixedGroup_le_adjointGroup _ _ _ (graphFixedRootGroup_le _ _ _ hg)
  have hmemJ : ∀ g : C, (g : ModGL TwistTag.D4.tag K) ∈ trialityFieldImage σ δ ↔
      fieldActor σ δ g = g := by
    intro g
    constructor
    · rintro ⟨g', -, hg'⟩
      refine Subtype.ext ?_
      rw [coe_fieldActor, ← hg']
      have hcomp : δ.toRingHom.comp (fixSubfield δ).subtype = (fixSubfield δ).subtype :=
        RingHom.ext fun x => x.2
      rw [units_map_entrywiseHom_eq_baseChangeGL, baseChangeGL_baseChangeGL, hcomp]
    · intro h
      rw [← htw, mem_twistedFixedGroup_iff_twistHom]
      refine ⟨hCadj g.2, ?_⟩
      have hg := (mem_twistedFixedGroup_iff_twistHom TwistTag.D4 K σ.toRingHom).1
        (graphFixedRootGroup_le _ _ _ g.2)
      have hδg : Units.map (entrywiseHom δ.toRingHom) (g : ModGL TwistTag.D4.tag K) = g :=
        congrArg Subtype.val h
      rw [twistHom_apply] at hg ⊢
      rw [show (σ * δ).toRingHom = σ.toRingHom.comp δ.toRingHom from RingHom.ext fun _ => rfl,
        ← units_map_entrywiseHom_comp, hδg]
      exact hg.2
  have hsimple₀ : IsSimpleGroup (graphFixedRootGroup TwistTag.D4 (fixSubfield δ)
        (fixSubfieldRestrict σ δ).toRingHom) ∧
      ∃ x y : graphFixedRootGroup TwistTag.D4 (fixSubfield δ)
        (fixSubfieldRestrict σ δ).toRingHom, x * y ≠ y * x := by
    by_cases h2 : ℓ = 2
    · have h4 : 4 ≤ Nat.card (fixSubfield δ) := by
        rw [hk, h2]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (3 * d) := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact isSimpleGroup_graphFixedRootGroup_of_perfect TwistTag.D4 _ _
        (commutator_graphFixedRootGroup_triality_char_two (hcharK₀.trans h2) _ hσ₀3 h4)
    · obtain ⟨h1, h2', -⟩ := odd_diagram_field_fixed_p_components TwistTag.D4 (fixSubfield δ)
        (by rw [hcharK₀]; exact h2) (fixSubfieldRestrict σ δ)
      exact ⟨h1, h2'⟩
  have hιinj : Function.Injective (baseChangeGL (τ := TwistTag.D4.tag) (fixSubfield δ).subtype) :=
    baseChangeGL_injective _
  set e := Subgroup.equivMapOfInjective (graphFixedRootGroup TwistTag.D4 (fixSubfield δ)
    (fixSubfieldRestrict σ δ).toRingHom) _ hιinj with he
  have hsimpleJ : IsSimpleGroup (trialityFieldImage σ δ) := by
    have := hsimple₀.1
    exact e.symm.isSimpleGroup
  have hncJ : ¬∀ a b : trialityFieldImage σ δ, a * b = b * a := by
    intro h
    obtain ⟨x, y, hxy⟩ := hsimple₀.2
    apply hxy
    apply e.injective
    rw [map_mul, map_mul]
    exact h _ _
  have hK' : Nat.card K = (ℓ ^ (d * m)) ^ 3 := by
    rw [hK, ← pow_mul, show d * m * 3 = 3 * d * m by ring]
  have hdm : 1 ≤ d * m := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hNF : ∀ α : MulAut C, ∃! gφ : C × (K ≃+* K),
      α = MulAut.conj gφ.1 * fieldActor σ gφ.2 := by
    by_cases h2 : ℓ = 2
    · subst h2
      exact (even_triality_exact_automorphism_normal_form hdm K hK' σ hσ).2.1
    · exact (odd_triality_exact_automorphism_normal_form hℓ h2 hdm K hK' σ hσ).2.1
  have hZ : Subgroup.center C = ⊥ := exceptional_fixed_center_trivial TwistTag.D4 K σ
  have hinj := mulAut_conj_injective_of_center_eq_bot hZ
  have hactinj : Function.Injective (fieldActorHom (t := TwistTag.D4) σ) := by
    rw [injective_iff_map_eq_one]
    intro φ h
    have h' : MulAut.conj (1 : C) * fieldActor σ φ = MulAut.conj (1 : C) * fieldActor σ 1 := by
      rw [fieldActor_one, map_one, one_mul, one_mul]
      exact h
    exact (conj_mul_fieldActor_injective_D4 σ hσ3pt h').2
  have hδ₀ord : orderOf (fieldActor (t := TwistTag.D4) σ δ) = m := by
    rw [← fieldActorHom_apply, orderOf_injective _ hactinj δ, hδord]
  have hcommδ : ∀ φ : K ≃+* K, fieldActor σ φ * fieldActor σ δ =
      fieldActor σ δ * fieldActor σ φ := fun φ => by
    rw [← fieldActor_mul (t := TwistTag.D4), ← fieldActor_mul (t := TwistTag.D4),
      (commute_ringEquiv_of_finite φ δ).eq]
  have hcentJ : ∀ β ∈ Subgroup.centralizer {fieldActor σ δ}, ∀ (g : C) (φ : K ≃+* K),
      β = MulAut.conj g * fieldActor σ φ →
        (g : ModGL TwistTag.D4.tag K) ∈ trialityFieldImage σ δ := by
    intro β hβ g φ h
    have hβδ : fieldActor σ δ * β = β * fieldActor σ δ :=
      Subgroup.mem_centralizer_iff.1 hβ _ (Set.mem_singleton _)
    rw [h] at hβδ
    have e1 : MulAut.conj (fieldActor σ δ g) * (fieldActor σ δ * fieldActor σ φ) =
        MulAut.conj g * (fieldActor σ δ * fieldActor σ φ) := by
      calc MulAut.conj (fieldActor σ δ g) * (fieldActor σ δ * fieldActor σ φ) =
          fieldActor σ δ * (MulAut.conj g * fieldActor σ φ) := by
            rw [← mul_assoc, ← mulAut_mul_conj, mul_assoc]
        _ = MulAut.conj g * fieldActor σ φ * fieldActor σ δ := hβδ
        _ = MulAut.conj g * (fieldActor σ δ * fieldActor σ φ) := by rw [mul_assoc, hcommδ]
    exact (hmemJ g).2 (hinj (mul_right_cancel e1))
  have hNδ : trialityFieldInner σ δ ≤ Subgroup.centralizer {fieldActor σ δ} := by
    rintro _ ⟨j, hj, rfl⟩
    refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    rw [Set.mem_singleton_iff.1 hh, mulAut_mul_conj,
      (hmemJ j).1 (Subgroup.mem_subgroupOf.1 hj)]
  refine ⟨hδ₀ord, fun c => by rw [mem_fixSubfield, hδ], hk, coe_fixSubfieldRestrict σ δ, hord,
    hJC, ?_, hsimpleJ, hncJ,
    ⟨((trialityFieldImage σ δ).subgroupOf C).equivMapOfInjective _ hinj, fun j => rfl⟩,
    fun β hβ => ?_, hNδ, ⟨fun n hn g => ?_⟩, le_antisymm (fun β hβ => ?_) ?_,
    by rw [Nat.card_zpowers, hδ₀ord]⟩
  ·
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact (hmemJ g).2 hg
    · intro hx
      exact ⟨⟨x, hJC hx⟩, (hmemJ _).1 hx, rfl⟩
  ·
    obtain ⟨⟨g, φ⟩, hgφ, huniq⟩ := hNF β
    exact ⟨(g, φ), ⟨hcentJ β hβ g φ hgφ, hgφ⟩, fun q hq => huniq q hq.2⟩
  ·
    obtain ⟨j, hj, hjn⟩ := Subgroup.mem_subgroupOf.1 hn
    rw [SetLike.mem_coe] at hj
    have hgδ : fieldActor σ δ * (g : MulAut C) = (g : MulAut C) * fieldActor σ δ :=
      Subgroup.mem_centralizer_iff.1 g.2 _ (Set.mem_singleton _)
    refine Subgroup.mem_subgroupOf.2 ⟨(g : MulAut C) j, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, hmemJ]
      calc fieldActor σ δ ((g : MulAut C) j) =
            (fieldActor σ δ * (g : MulAut C) : MulAut C) j := rfl
        _ = ((g : MulAut C) * fieldActor σ δ : MulAut C) j := by rw [hgδ]
        _ = (g : MulAut C) (fieldActor σ δ j) := rfl
        _ = (g : MulAut C) j := by rw [(hmemJ j).1 (Subgroup.mem_subgroupOf.1 hj)]
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hjn]
      exact (mulAut_mul_conj_mul_inv _ _).symm
  ·
    obtain ⟨hβδ, hβN⟩ := Subgroup.mem_inf.1 hβ
    obtain ⟨⟨g, φ⟩, hgφ, -⟩ := hNF β
    have hgJ := hcentJ β hβδ g φ hgφ
    have hfix : ∀ j : C, (j : ModGL TwistTag.D4.tag K) ∈ trialityFieldImage σ δ → β j = j := by
      intro j hj
      have hn : MulAut.conj j ∈ trialityFieldInner σ δ :=
        ⟨j, Subgroup.mem_subgroupOf.2 hj, rfl⟩
      have h1 : MulAut.conj j * β = β * MulAut.conj j :=
        Subgroup.mem_centralizer_iff.1 hβN _ hn
      have h2 : MulAut.conj (β j) = MulAut.conj j := by
        rw [← mulAut_mul_conj_mul_inv, ← h1, mul_inv_cancel_right]
      exact hinj h2
    obtain ⟨g', hg', hgg'⟩ := hgJ
    have hid : MulAut.conj (⟨g', hg'⟩ : graphFixedRootGroup TwistTag.D4 (fixSubfield δ)
        (fixSubfieldRestrict σ δ).toRingHom) *
          fieldActor (fixSubfieldRestrict σ δ) (fixSubfieldRestrict φ δ) = 1 := by
      refine MulEquiv.ext fun j' => Subtype.ext ?_
      have hj'J : baseChangeGL (fixSubfield δ).subtype (j' : ModGL TwistTag.D4.tag
          (fixSubfield δ)) ∈ trialityFieldImage σ δ := ⟨j', j'.2, rfl⟩
      have h1 := congrArg Subtype.val (hfix ⟨_, hJC hj'J⟩ hj'J)
      rw [hgφ] at h1
      change (g : ModGL TwistTag.D4.tag K) * Units.map (entrywiseHom φ.toRingHom)
        (baseChangeGL (fixSubfield δ).subtype (j' : ModGL TwistTag.D4.tag (fixSubfield δ))) *
          (g : ModGL TwistTag.D4.tag K)⁻¹ =
        baseChangeGL (fixSubfield δ).subtype (j' : ModGL TwistTag.D4.tag (fixSubfield δ)) at h1
      rw [← hgg', entrywise_baseChangeGL_fixSubfieldRestrict, ← map_inv, ← map_mul,
        ← map_mul] at h1
      exact hιinj h1
    obtain ⟨hg1, hψ1⟩ := conj_mul_fieldActor_injective_D4 (fixSubfieldRestrict σ δ) hσ₀3
      (g' := 1) (δ' := 1) (by rw [hid, map_one, fieldActor_one, one_mul])
    have hg1' : g = 1 := Subtype.ext (by
      rw [← hgg', show g' = 1 from congrArg Subtype.val hg1, map_one]
      rfl)
    have hφK₀ : ∀ x, δ x = x → φ x = x := fun x hx => by
      have h2 := congrArg (fun ψ : fixSubfield δ ≃+* fixSubfield δ => (ψ ⟨x, hx⟩ : K)) hψ1
      exact h2
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1
      (CFSG.ComponentClassification.UnbalancedCatalog.mem_zpowers_of_fixed hφK₀)
    refine Subgroup.mem_zpowers_iff.2 ⟨n, ?_⟩
    rw [hgφ, hg1', map_one, one_mul]
    exact (map_zpow (fieldActorHom (t := TwistTag.D4) σ) δ n).symm
  ·
    refine Subgroup.zpowers_le.2 (Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2
      fun h hh => by rw [Set.mem_singleton_iff.1 hh], Subgroup.mem_centralizer_iff.2
        fun n hn => (Subgroup.mem_centralizer_iff.1 (hNδ hn) _ (Set.mem_singleton _)).symm⟩)

end CFSG.RankThree.Chevalley
