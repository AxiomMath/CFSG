module

public import CFSG.Milestones.ASVolI.F429.bC6
public import CFSG.Milestones.ASVolI.F429.bC5D4
public import CFSG.LieType.Chevalley.EvenTrialityCanonicalFieldCentralizer

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin

section Transport

variable {E : Type} [Group E] {Gp : Subgroup E} [Gp.Normal] {C : Type} [Group C]

theorem burnsideF429b_conjAut_one (Ψ : C ≃* ↥Gp) :
    (Ψ.trans (burnsideF4d_rho Gp 1)).trans Ψ.symm = 1 := by
  refine MulEquiv.ext fun c => Ψ.injective (Subtype.ext ?_)
  rw [burnsideF429b_conjAut_apply, MulAut.one_apply]
  group

theorem burnsideF429b_conjAut_pow (Ψ : C ≃* ↥Gp) (x : E) (n : ℕ) :
    (Ψ.trans (burnsideF4d_rho Gp (x ^ n))).trans Ψ.symm =
      ((Ψ.trans (burnsideF4d_rho Gp x)).trans Ψ.symm) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, burnsideF429b_conjAut_one]
  | succ n ih => rw [pow_succ, pow_succ, burnsideF429b_conjAut_mul, ih]

end Transport

section D4Rank

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds


theorem burnsideF429b_trialityD4_rank_le' {e : ℕ} (he : 1 ≤ e) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ e) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ ((2 ^ e) ^ 2)) :
    ∀ B : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
        Nat.card B ≤ 2 * (2 ^ e) ^ 5 := by
  have hK' : Nat.card K = 2 ^ (3 * e) := by rw [hK, ← pow_mul, mul_comm]
  haveI : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hK'
  have hpc : ∀ c : K, c ^ ((2 ^ e) ^ 3) = c := fun c => by
    haveI := Fintype.ofFinite K
    rw [← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hcube : ∀ c, σ (σ (σ c)) = c := fun c => by
    rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul]
    have e6 : (2 ^ e) ^ 2 * ((2 ^ e) ^ 2 * (2 ^ e) ^ 2) = (2 ^ e) ^ 3 * (2 ^ e) ^ 3 := by ring
    rw [e6, pow_mul, hpc, hpc]
  have hσ3 : σ.toRingHom ^ 3 = 1 := by
    ext c
    simp only [pow_succ, pow_zero, one_mul, RingHom.mul_def, RingHom.comp_apply,
      RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingHom.id_apply]
    exact hcube c
  have hσ3E : σ ^ 3 = 1 :=
    RingEquiv.ext fun c => by
      change σ (σ (σ c)) = c
      exact hcube c
  have hkcard : Nat.card (trialityFixedField K σ.toRingHom) = 2 ^ e := by
    obtain ⟨-, -, -, hL2, -⟩ := triality_all_characteristic_faithful_torus_coordinates K σ hσ3E
    have hcardL := card_orbitField_D4_orientation (K := K) Nat.prime_two he hK (r := 2)
      (Or.inr rfl) (σ := σ.toRingHom) (fun c => by show σ c = _; rw [hσ c]) ⟨1, by decide⟩
    rw [← hL2, hcardL, show (TwistTag.D4.orbit ⟨1, by decide⟩).card = 1 by decide, pow_one]
  have hK3 : Nat.card K = Nat.card (trialityFixedField K σ.toRingHom) ^ 3 := by
    rw [hkcard, hK]
  obtain ⟨D⟩ := exists_d4Syl K σ hσ3
  haveI : Finite (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) :=
    Finite.of_surjective _ D.bij.2
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Psyl, hsyl⟩⟩ :=
    even_triality_positive_orbit_parametrization K σ hσ3
  haveI : Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    Finite.of_injective (fun g => (g : ModGL TwistTag.D4.tag K)) Subtype.val_injective
  have hle : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
  let e' : (Psyl : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ≃*
      graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom :=
    (MulEquiv.subgroupCongr hsyl).trans (Subgroup.subgroupOfEquivOfLe hle)
  refine rank_le_of_sylow Psyl (rank_transport_N e' fun B hc h2 => ?_)
  have := D.card_elemAbelian_le hK3 B hc h2
  rwa [hkcard] at this

theorem burnsideF429b_D4_card_fixed_le {e : ℕ} (he : 1 ≤ e) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (6 * e)) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ (2 * e))
    (δ : K ≃+* K) (hδ : ∀ c, δ c = c ^ 2 ^ (3 * e))
    (B : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (h2 : ∀ x ∈ B, x * x = 1)
    (hfix : ∀ x ∈ B, fieldActor σ δ x = x) :
    Nat.card B ≤ 2 * (2 ^ e) ^ 5 := by
  obtain ⟨-, hk, hres, -, hJle, hJ, -⟩ :=
    even_triality_canonical_field_full_centralizer he K hK σ hσ δ hδ
  haveI : Finite (fixSubfield δ) := Subtype.finite
  let ι : graphFixedRootGroup TwistTag.D4 (fixSubfield δ) (fixSubfieldRestrict σ δ).toRingHom →*
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    ((baseChangeGL (fixSubfield δ).subtype).comp
      (graphFixedRootGroup TwistTag.D4 (fixSubfield δ)
        (fixSubfieldRestrict σ δ).toRingHom).subtype).codRestrict _
      (fun y => hJle ⟨y, y.2, rfl⟩)
  have hι : Function.Injective ι := fun a b hab =>
    Subtype.ext (baseChangeGL_injective _ (congrArg Subtype.val hab))
  have hrange : B ≤ ι.range := by
    intro x hx
    have hxJ : (x : ModGL TwistTag.D4.tag K) ∈ trialityFieldImage σ δ := by
      rw [← hJ]
      exact ⟨x, hfix x hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hxJ
    exact ⟨⟨y, hy⟩, Subtype.ext hyx⟩
  have hcard : Nat.card (B.comap ι) = Nat.card B := by
    rw [← Subgroup.card_map_of_injective hι, Subgroup.map_comap_eq_self hrange]
  rw [← hcard]
  have hK₀ : Nat.card (fixSubfield δ) = (2 ^ e) ^ 3 := by rw [hk, ← pow_mul, mul_comm]
  have hσ₀ : ∀ c : fixSubfield δ, fixSubfieldRestrict σ δ c = c ^ ((2 ^ e) ^ 2) := fun c =>
    Subtype.ext (by
      rw [hres, hσ, SubmonoidClass.coe_pow, ← pow_mul, mul_comm e 2])
  exact burnsideF429b_trialityD4_rank_le' he (fixSubfield δ) hK₀ (fixSubfieldRestrict σ δ) hσ₀ _
    (fun x hx y hy => hι (by rw [map_mul, map_mul]; exact hab _ hx _ hy))
    (fun x hx => hι (by rw [map_mul, map_one]; exact h2 _ hx))

end D4Rank

section D4Roots

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Quasithin.H13.F431.D4q.Struct
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootChar)


theorem burnsideF429b_D4_root_data {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)
    (hσ3 : σ.toRingHom ^ 3 = 1) :
    ∃ (X4 : Multiplicative K →* Cm σ)
      (X6 : Multiplicative (trialityFixedField K σ.toRingHom) →* Cm σ),
      (∀ c, ((X6 (Multiplicative.ofAdd c) : Cm σ) : ModGL TwistTag.D4.tag K) =
        pinnedX TwistTag.D4.tag K (trialityRoot 5) c) ∧
      (∀ c, X4 c ∈ Ust σ) ∧ (∀ c, X6 c ∈ Ust σ) ∧
      (∀ c d, X4 c * X6 d = X6 d * X4 c) ∧
      (∀ c, ∀ u ∈ Ust σ, u * X6 c = X6 c * u) ∧
      Function.Injective (fun p : Multiplicative K × Multiplicative (trialityFixedField K σ.toRingHom) =>
        X4 p.1 * X6 p.2) := by
  obtain ⟨⟨f1, -, hf1⟩, ⟨f2, -, hf2⟩, ⟨f3, -, hf3⟩, ⟨f4, -, hf4⟩, ⟨f5, -, hf5⟩, ⟨f6, -, hf6⟩,
    hbij, -, -⟩ := even_triality_positive_orbit_parametrization K σ hσ3
  obtain ⟨-, -, -, -, c16, -, -, c26, -, c36, -, c46, c56, -, -⟩ :=
    even_triality_trace_commutators K σ.toRingHom hσ3
  have hle : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
  set X4 : Multiplicative K →* Cm σ := (Subgroup.inclusion hle).comp f4 with hX4def
  set X6 : Multiplicative (trialityFixedField K σ.toRingHom) →* Cm σ :=
    (Subgroup.inclusion hle).comp f6 with hX6def
  have hX4 : ∀ c : Multiplicative K, ((X4 c : Cm σ) : ModGL TwistTag.D4.tag K) =
      trialityX₄ K σ.toRingHom (Multiplicative.toAdd c) := fun c => hf4 (Multiplicative.toAdd c)
  have hX6 : ∀ c : Multiplicative (trialityFixedField K σ.toRingHom),
      ((X6 c : Cm σ) : ModGL TwistTag.D4.tag K) =
        trialityX₆ K σ.toRingHom (Multiplicative.toAdd c) := fun c => hf6 (Multiplicative.toAdd c)
  have c66 : ∀ a b : trialityFixedField K σ.toRingHom,
      Commute (trialityX₆ K σ.toRingHom a) (trialityX₆ K σ.toRingHom b) := by
    intro a b
    have hc' : Commute (f6 (Multiplicative.ofAdd a)) (f6 (Multiplicative.ofAdd b)) :=
      (Commute.all _ _).map f6
    apply Subtype.ext
    show (trialityX₆ K σ.toRingHom a : ModGL TwistTag.D4.tag K) * trialityX₆ K σ.toRingHom b =
      (trialityX₆ K σ.toRingHom b : ModGL TwistTag.D4.tag K) * trialityX₆ K σ.toRingHom a
    rw [← hf6 a, ← hf6 b, ← Subgroup.coe_mul, ← Subgroup.coe_mul, hc'.eq]
  have z1 : (trialityX₁ K σ.toRingHom 0 : ModGL TwistTag.D4.tag K) = 1 := by
    rw [← hf1 0, ofAdd_zero, map_one]
    rfl
  have z2 : (trialityX₂ K σ.toRingHom 0 : ModGL TwistTag.D4.tag K) = 1 := by
    rw [← hf2 0, ofAdd_zero, map_one]
    rfl
  have z3 : (trialityX₃ K σ.toRingHom 0 : ModGL TwistTag.D4.tag K) = 1 := by
    rw [← hf3 0, ofAdd_zero, map_one]
    rfl
  have z5 : (trialityX₅ K σ.toRingHom 0 : ModGL TwistTag.D4.tag K) = 1 := by
    rw [← hf5 0, ofAdd_zero, map_one]
    rfl
  refine ⟨X4, X6, fun c => hf6 c, fun c => (f4 c).2, fun c => (f6 c).2, fun c d => ?_,
    fun c u hu => ?_, ?_⟩
  · apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hX4, hX6, ← Subgroup.coe_mul, ← Subgroup.coe_mul,
      (c46 (Multiplicative.toAdd c) (Multiplicative.toAdd d)).eq]
  · obtain ⟨p, -, hp⟩ := hbij.2.2 (show (u : ModGL TwistTag.D4.tag K) ∈
      graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom from hu)
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hp, hX6]
    dsimp only
    have hc : Commute (trialityX₁ K σ.toRingHom p.1 * trialityX₂ K σ.toRingHom p.2.1 *
        trialityX₃ K σ.toRingHom p.2.2.1 * trialityX₄ K σ.toRingHom p.2.2.2.1 *
        trialityX₅ K σ.toRingHom p.2.2.2.2.1 * trialityX₆ K σ.toRingHom p.2.2.2.2.2)
        (trialityX₆ K σ.toRingHom (Multiplicative.toAdd c)) :=
      (((((c16 _ _).mul_left (c26 _ _)).mul_left (c36 _ _)).mul_left (c46 _ _)).mul_left
        (c56 _ _)).mul_left (c66 _ _)
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hc.eq]
  · rintro ⟨d, f⟩ ⟨d', f'⟩ h
    have h' := congrArg (fun x : Cm σ => (x : ModGL TwistTag.D4.tag K)) h
    simp only [Subgroup.coe_mul, hX4, hX6] at h'
    have hpq : (0, 0, 0, Multiplicative.toAdd d, 0, Multiplicative.toAdd f) =
        ((0, 0, 0, Multiplicative.toAdd d', 0, Multiplicative.toAdd f') :
          K × trialityFixedField K σ.toRingHom × K × K × trialityFixedField K σ.toRingHom ×
            trialityFixedField K σ.toRingHom) := by
      refine hbij.injOn (Set.mem_univ _) (Set.mem_univ _) ?_
      simp only [Subgroup.coe_mul, z1, z2, z3, z5, one_mul, mul_one]
      exact h'
    simp only [Prod.mk.injEq, true_and] at hpq
    rw [show d = d' from hpq.1, show f = f' from hpq.2]

theorem burnsideF429b_D4_exists_R0 {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)
    (hσ3 : σ.toRingHom ^ 3 = 1) :
    ∃ R : Subgroup (Cm σ), R ≤ Ust σ ∧ (∀ x ∈ R, ∀ y ∈ R, x * y = y * x) ∧
      (∀ x ∈ R, x * x = 1) ∧
      Nat.card K * Nat.card (trialityFixedField K σ.toRingHom) ≤ Nat.card R := by
  obtain ⟨X4, X6, -, hX4U, hX6U, h46, -, hinj⟩ := burnsideF429b_D4_root_data σ hσ3
  have hmul : ∀ (d d' : Multiplicative K) (f f' : Multiplicative (trialityFixedField K σ.toRingHom)),
      X4 d * X6 f * (X4 d' * X6 f') = X4 (d * d') * X6 (f * f') := by
    intro d d' f f'
    calc X4 d * X6 f * (X4 d' * X6 f') = X4 d * (X6 f * X4 d') * X6 f' := by
          simp only [mul_assoc]
      _ = X4 d * (X4 d' * X6 f) * X6 f' := by rw [h46]
      _ = X4 (d * d') * X6 (f * f') := by rw [map_mul, map_mul]; simp only [mul_assoc]
  let R : Subgroup (Cm σ) :=
    { carrier := {g | ∃ d f, g = X4 d * X6 f}
      mul_mem' := by
        rintro _ _ ⟨d, f, rfl⟩ ⟨d', f', rfl⟩
        exact ⟨d * d', f * f', hmul ..⟩
      one_mem' := ⟨1, 1, by rw [map_one, map_one, one_mul]⟩
      inv_mem' := by
        rintro _ ⟨d, f, rfl⟩
        refine ⟨d⁻¹, f⁻¹, ?_⟩
        rw [mul_inv_rev, ← map_inv, ← map_inv, h46] }
  have hsqK : ∀ d : Multiplicative K, d * d = 1 := fun d => by
    show Multiplicative.ofAdd (Multiplicative.toAdd d + Multiplicative.toAdd d) = Multiplicative.ofAdd 0
    rw [CharTwo.add_self_eq_zero]
  have hsqk : ∀ f : Multiplicative (trialityFixedField K σ.toRingHom), f * f = 1 := fun f => by
    show Multiplicative.ofAdd (Multiplicative.toAdd f + Multiplicative.toAdd f) = Multiplicative.ofAdd 0
    rw [CharTwo.add_self_eq_zero]
  refine ⟨R, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨d, f, rfl⟩
    exact mul_mem (hX4U d) (hX6U f)
  · rintro _ ⟨d, f, rfl⟩ _ ⟨d', f', rfl⟩
    rw [hmul, hmul, mul_comm d, mul_comm f]
  · rintro _ ⟨d, f, rfl⟩
    rw [hmul, hsqK, hsqk, map_one, map_one, one_mul]
  · let φ : Multiplicative K × Multiplicative (trialityFixedField K σ.toRingHom) → R :=
      fun p => ⟨X4 p.1 * X6 p.2, p.1, p.2, rfl⟩
    have hφ : Function.Injective φ := fun p p' h => hinj (congrArg Subtype.val h)
    calc Nat.card K * Nat.card (trialityFixedField K σ.toRingHom) =
        Nat.card (Multiplicative K × Multiplicative (trialityFixedField K σ.toRingHom)) := by
          rw [Nat.card_prod]
          rfl
      _ ≤ Nat.card R := Nat.card_le_card_of_injective φ hφ

theorem burnsideF429b_D4_fix_k_of_fix_X6 {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    {u h : Cm σ} (hu : u ∈ Ust σ)
    (hh : (h : ModGL TwistTag.D4.tag K) ∈ torusGroup TwistTag.D4.tag K) (ε : K ≃+* K)
    {X6 : Multiplicative (trialityFixedField K σ.toRingHom) →* Cm σ}
    (hX6 : ∀ c, ((X6 (Multiplicative.ofAdd c) : Cm σ) : ModGL TwistTag.D4.tag K) =
      pinnedX TwistTag.D4.tag K (trialityRoot 5) c)
    (hcent : ∀ c, ∀ v ∈ Ust σ, v * X6 c = X6 c * v)
    (hfix : ∀ c, u * h * fieldActor σ ε (X6 c) * (u * h)⁻¹ = X6 c) :
    ∀ c ∈ trialityFixedField K σ.toRingHom, ε c = c := by
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  have key : ∀ c : trialityFixedField K σ.toRingHom,
      (rootChar a (trialityRoot 5) : K) * ε c = c := by
    intro c
    have e1 : h * fieldActor σ ε (X6 (Multiplicative.ofAdd c)) * h⁻¹ =
        X6 (Multiplicative.ofAdd c) := by
      have h1 := hfix (Multiplicative.ofAdd c)
      have hc := hcent (Multiplicative.ofAdd c) u⁻¹ (inv_mem hu)
      calc h * fieldActor σ ε (X6 (Multiplicative.ofAdd c)) * h⁻¹ =
          u⁻¹ * (u * h * fieldActor σ ε (X6 (Multiplicative.ofAdd c)) * (u * h)⁻¹) * u := by
            group
        _ = u⁻¹ * X6 (Multiplicative.ofAdd c) * u := by rw [h1]
        _ = X6 (Multiplicative.ofAdd c) * u⁻¹ * u := by rw [hc]
        _ = X6 (Multiplicative.ofAdd c) := by group
    have e2 := congrArg (fun y : Cm σ => (y : ModGL TwistTag.D4.tag K)) e1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_fieldActor, hX6, ha] at e2
    have e3 : Units.map (entrywiseHom ε.toRingHom)
        (pinnedX TwistTag.D4.tag K (trialityRoot 5) (c : K)) =
        pinnedX TwistTag.D4.tag K (trialityRoot 5) (ε c) :=
      Units.ext (entrywise_pinnedX ε.toRingHom _ _)
    rw [e3, rootDiagUnit_conj_pinnedX a (isRoot_trialityRoot' 5)] at e2
    exact pinnedX_injective _ _ _ e2
  have hχ : (rootChar a (trialityRoot 5) : K) = 1 := by
    simpa using key 1
  intro c hc
  have := key ⟨c, hc⟩
  rwa [hχ, one_mul] at this

end D4Roots

section C6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Quasithin.H13.F431.D4q.Struct


theorem burnsideF429b_c6_D4tw {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .D4tw 2 f Gp M₁ M₂) (hf : 2 ≤ f) {T : Subgroup E}
    (hT : ChF.IsSylowOf 2 T (M₁ ⊓ M₂)) : burnsideF429_C6 .D4tw f Gp M₁ M₂ T := by
  haveI := hyp.finite
  haveI := hyp.normal
  obtain ⟨K, fK, finK, cK, σ, hσ3', hf1, hK, hσq, Ψ, h1, h2⟩ :=
    burnsideF429b_D4_chart hyp.toHypF_4_4g
  have hσ' : ∀ c, σ c = c ^ (2 ^ f) := hσq
  have hσ3 : σ.toRingHom ^ 3 = 1 :=
    RingHom.ext fun c => (ringHom_pow_three_apply σ.toRingHom c).trans (hσ3' c)
  have hσ3E : σ ^ 3 = 1 := RingEquiv.ext fun c => by
    change σ (σ (σ c)) = c
    exact hσ3' c
  set S := pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) with hSdef
  set φ : Cm σ →* E := Gp.subtype.comp Ψ.toMonoidHom with hφdef
  have hφ : Function.Injective φ := Gp.subtype_injective.comp Ψ.injective
  have hφx : ∀ x, φ x = ((Ψ x : ↥Gp) : E) := fun x => rfl
  have hGB : Gp ⊓ (M₁ ⊓ M₂) = (Pst0 σ ⊓ Pst1 σ).map φ :=
    burnsideF429_inf_eq_map Ψ (burnsideF429b_inf_subgroupOf Ψ h1 h2)
  have hS : S = (Ust σ).map φ := by
    rw [hSdef, hGB, CFSG.Quasithin.H13.F431.pCoreOf_map_of_injective _ hφ,
      burnsideF429b_D4_pCore_B σ hf1 hK hσq]
  have hmemS : ∀ x, x ∈ T → x ∈ Gp → x ∈ S := fun x hx hg => by
    rw [hSdef, ← burnsideF429_T_inf_Gp hyp hT]
    exact ⟨hx, hg⟩
  have hc := hyp.centralizer_trivial
  have hkq : Nat.card (trialityFixedField K σ.toRingHom) = 2 ^ f :=
    burnsideF429b_D4_card_fixed σ hf1 hK hσq
  obtain ⟨X4, X6, hX6, -, hX6U, -, hcent, -⟩ := burnsideF429b_D4_root_data σ hσ3
  obtain ⟨R₀, hR₀U, hR₀c, hR₀2, hR₀card⟩ := burnsideF429b_D4_exists_R0 σ hσ3
  have hRcard : 2 ^ (4 * f) ≤ Nat.card ↥(R₀.map φ) := by
    rw [Subgroup.card_map_of_injective hφ]
    calc 2 ^ (4 * f) = Nat.card K * Nat.card (trialityFixedField K σ.toRingHom) := by
          rw [hK, hkq]; ring
      _ ≤ Nat.card R₀ := hR₀card
  have D := CFSG.Quasithin.H13.Sec53F.TriD4.borelAutData_d4 σ hf1 hK hσ'
  refine burnsideF429_c6_of' (R := R₀.map φ) (W := X6.range.map φ)
    (burnsideF429_sbar_le hT) ?_ (burnsideF429b_isElemAbelian_map φ hR₀c hR₀2) ?_ ?_ ?_ ?_ ?_
  ·
    rw [← hSdef, hS]
    exact Subgroup.map_mono hR₀U
  ·
    intro A hAT hAe hAS
    obtain ⟨t, htA, htS⟩ := SetLike.not_le_iff_exists.1 hAS
    have hinvA : ∀ a ∈ A, a * a = 1 := fun a ha => by rw [← sq]; exact hAe.2 a ha
    have hcommA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := isMulCommutative_iff_of_setLike.mp hAe.1
    have hnotG : ∀ a ∈ A, a ∉ S → a ∉ Gp := fun a ha haS haG => haS (hmemS a (hAT ha) haG)
    obtain ⟨-, -, ⟨Θ, -, -, hker, hinv⟩, -⟩ :=
      even_triality_exact_automorphism_normal_form hf1 K hK σ hσ'
    have hα2 : ∀ a ∈ A, ((Ψ.trans (burnsideF4d_rho Gp a)).trans Ψ.symm) ^ 2 = 1 :=
      fun a ha => by rw [sq]; exact burnsideF429b_conjAut_sq Ψ (hinvA a ha)
    have hΘ : ∀ a ∈ A, a ∉ S →
        ∀ c, Θ ((Ψ.trans (burnsideF4d_rho Gp a)).trans Ψ.symm) c = c ^ (2 ^ (3 * f / 2)) := by
      intro a ha haS
      rcases hinv _ (hα2 a ha) with h1 | ⟨-, hc'⟩
      · exfalso
        apply burnsideF429b_conjAut_not_inner hc Ψ (hnotG a ha haS)
        show _ ∈ (MulAut.conj : Cm σ →* MulAut (Cm σ)).range
        rw [← hker]
        exact MonoidHom.mem_ker.2 h1
      · exact hc'
    have hA1 : Nat.card A ≤ 2 * Nat.card ↥(A ⊓ S) := by
      refine burnsideF429b_card_le_two_mul htA fun a ha haS => ?_
      refine hmemS _ (hAT (A.mul_mem htA ha)) (burnsideF429b_mem_of_conjAut_inner hc Ψ ?_)
      show _ ∈ (MulAut.conj : Cm σ →* MulAut (Cm σ)).range
      rw [← hker, MonoidHom.mem_ker, burnsideF429b_conjAut_mul, map_mul]
      have e : Θ ((Ψ.trans (burnsideF4d_rho Gp t)).trans Ψ.symm) =
          Θ ((Ψ.trans (burnsideF4d_rho Gp a)).trans Ψ.symm) :=
        RingEquiv.ext fun c => by rw [hΘ t htA htS, hΘ a ha haS]
      rw [e, ← map_mul, ← sq, hα2 a ha, map_one]
    obtain ⟨⟨m, hm⟩, δ, k, hδ, -, hαk⟩ := burnsideF429b_D4_outer_involution hf1 K hK σ hσ' _
      (burnsideF429b_conjAut_sq Ψ (hinvA t htA))
      (burnsideF429b_conjAut_not_inner hc Ψ (hnotG t htA htS))
    have hm1 : 1 ≤ m := by omega
    have hK6 : Nat.card K = 2 ^ (6 * m) := by rw [hK, hm]; ring
    have hσ6 : ∀ c, σ c = c ^ 2 ^ (2 * m) := fun c => by rw [hσ', hm, two_mul]
    have hδ6 : ∀ c, δ c = c ^ 2 ^ (3 * m) := fun c => by
      rw [hδ, show 3 * f / 2 = 3 * m by omega]
    have hle : A ⊓ S ≤ φ.range := fun y hy => by
      have hy' : y ∈ (Ust σ).map φ := hS ▸ hy.2
      obtain ⟨u, -, rfl⟩ := hy'
      exact ⟨u, rfl⟩
    have hBcard : Nat.card ↥(((A ⊓ S).comap φ).map (MulAut.conj k⁻¹).toMonoidHom) =
        Nat.card ↥(A ⊓ S) := by
      rw [Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective,
        ← Subgroup.card_map_of_injective hφ, Subgroup.map_comap_eq_self hle]
    have hB2 := burnsideF429b_D4_card_fixed_le hm1 hK6 σ hσ6 δ hδ6
      (((A ⊓ S).comap φ).map (MulAut.conj k⁻¹).toMonoidHom) ?_ ?_ ?_
    · calc Nat.card A ≤ 2 * Nat.card ↥(A ⊓ S) := hA1
        _ = 2 * Nat.card ↥(((A ⊓ S).comap φ).map (MulAut.conj k⁻¹).toMonoidHom) := by
            rw [hBcard]
        _ ≤ 2 * (2 * (2 ^ m) ^ 5) := Nat.mul_le_mul_left 2 hB2
        _ = 2 ^ (5 * m + 2) := by ring
        _ < 2 ^ (8 * m) := Nat.pow_lt_pow_right (by norm_num) (by omega)
        _ = 2 ^ (4 * f) := by rw [hm]; ring
        _ ≤ Nat.card ↥(R₀.map φ) := hRcard
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact hφ (by rw [map_mul, map_mul]; exact hcommA _ hx.1 _ hy.1)
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_mul]
      have hxx : x * x = 1 := hφ (by rw [map_mul, map_one]; exact hinvA _ hx.1)
      rw [hxx, map_one]
    · rintro _ ⟨y, hy, rfl⟩
      have hty : (Ψ.trans (burnsideF4d_rho Gp t)).trans Ψ.symm y = y :=
        burnsideF429b_conjAut_fix Ψ (by rw [← hφx]; exact hcommA t htA _ hy.1)
      have e : MulAut.conj k (fieldActor σ δ ((MulAut.conj k)⁻¹ y)) = y := by
        rw [hαk, MulAut.mul_apply, MulAut.mul_apply] at hty
        exact hty
      show fieldActor σ δ (MulAut.conj k⁻¹ y) = MulAut.conj k⁻¹ y
      rw [map_inv MulAut.conj k]
      calc fieldActor σ δ ((MulAut.conj k)⁻¹ y) =
          (MulAut.conj k)⁻¹ (MulAut.conj k (fieldActor σ δ ((MulAut.conj k)⁻¹ y))) := by
            rw [MulAut.inv_apply_self]
        _ = (MulAut.conj k)⁻¹ y := by rw [e]
  ·
    rw [← hSdef, hS]
    refine Subgroup.map_mono ?_
    rintro _ ⟨c, rfl⟩
    exact hX6U c
  ·
    rintro _ ⟨w, ⟨c, rfl⟩, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [← hSdef, hS] at hy
    obtain ⟨u, hu, rfl⟩ := hy
    rw [← map_mul, ← map_mul, hcent c u hu]
  ·
    rintro _ ⟨w, ⟨c, rfl⟩, rfl⟩
    have hcc : c * c = 1 := by
      show Multiplicative.ofAdd (Multiplicative.toAdd c + Multiplicative.toAdd c) =
        Multiplicative.ofAdd 0
      rw [CharTwo.add_self_eq_zero]
    rw [← map_pow, ← map_pow, sq, hcc, map_one, map_one]
  ·
    rintro x ⟨hxT, hxW⟩
    have hx12 : x ∈ M₁ ⊓ M₂ := hT.1 hxT
    have hrN := burnsideF429_le_normalizer_pCore_inf (Gp := Gp) (M₁ ⊓ M₂) hx12
    have hmemU : ∀ y : Cm σ, y ∈ Ust σ ↔ φ y ∈ S := by
      intro y
      rw [hS]
      exact (Subgroup.mem_map_iff_mem hφ).symm
    have h1' : ∀ y, (Ψ.trans (burnsideF4d_rho Gp x)).trans Ψ.symm y ∈ Ust σ ↔ y ∈ Ust σ := by
      intro y
      rw [hmemU, hmemU, hφx, hφx, burnsideF429b_conjAut_apply]
      exact ((Subgroup.mem_normalizer_iff.1 hrN) _).symm
    obtain ⟨g, hg, τ, ⟨ε, rfl⟩, hβ⟩ := D.normal_form _ h1'
    obtain ⟨u, hu, h, hh, rfl⟩ := D.B_eq g hg
    obtain ⟨n, hn⟩ : ∃ n : ℕ, x ^ 2 ^ n = 1 := by
      obtain ⟨n, hn⟩ := hT.2.1 ⟨x, hxT⟩
      exact ⟨n, congrArg Subtype.val hn⟩
    have hβn : ((Ψ.trans (burnsideF4d_rho Gp x)).trans Ψ.symm) ^ 2 ^ n = 1 := by
      rw [← burnsideF429b_conjAut_pow, hn, burnsideF429b_conjAut_one]
    have hτn : (fieldActorHom (t := TwistTag.D4) σ ε) ^ 2 ^ n = 1 := by
      obtain ⟨w, hw⟩ := burnsideF429b_pow_conj_mul (u * h) (fieldActorHom (t := TwistTag.D4) σ ε)
        (2 ^ n)
      rw [← hβ, hβn] at hw
      have e : (fieldActorHom (t := TwistTag.D4) σ ε) ^ 2 ^ n = MulAut.conj w⁻¹ := by
        rw [map_inv]
        exact eq_inv_of_mul_eq_one_right hw.symm
      exact burnsideF429b_eq_one_of_inner D
        (Subgroup.pow_mem _ (MonoidHom.mem_range.2 ⟨ε, rfl⟩) _) e
    have hεn : ε ^ 2 ^ n = 1 := burnsideF429b_D4_eq_one_of_fix_outer σ hσ3E (ε ^ 2 ^ n)
      fun a => by rw [map_pow, hτn]; rfl
    have hfix : ∀ c, u * h * fieldActor σ ε (X6 c) * (u * h)⁻¹ = X6 c := by
      intro c
      have e : (Ψ.trans (burnsideF4d_rho Gp x)).trans Ψ.symm (X6 c) = X6 c := by
        refine burnsideF429b_conjAut_fix Ψ ?_
        rw [← hφx]
        exact (Subgroup.mem_centralizer_iff.1 hxW _
          (Subgroup.mem_map_of_mem φ (MonoidHom.mem_range.2 ⟨c, rfl⟩))).symm
      rw [hβ, MulAut.mul_apply, MulAut.conj_apply, fieldActorHom_apply] at e
      exact e
    have hhT : (h : ModGL TwistTag.D4.tag K) ∈ torusGroup TwistTag.D4.tag K :=
      (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hh)).1).1
    have hk := burnsideF429b_D4_fix_k_of_fix_X6 σ hu hhT ε hX6 hcent hfix
    have hε1 := burnsideF429b_ringEquiv_eq_one _ (burnsideF429b_D4_finrank σ hf1 hK hσq) hk hεn
    rw [hε1, map_one, mul_one] at hβ
    exact hmemS x hxT (burnsideF429b_mem_of_conjAut_inner hc Ψ ⟨u * h, hβ.symm⟩)

end C6

end CFSG.ASVolI
