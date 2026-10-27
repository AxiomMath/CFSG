module

public import CFSG.Quasithin.Background.E6EighteenG
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentAlt
public import CFSG.LieType.Chevalley.EvenTrialityCanonicalFieldCentralizer
public import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
public import CFSG.LieType.Chevalley.TrialityCover
public import CFSG.LieType.Chevalley.TrialityFullAmbientFixedGroup
public import CFSG.LieType.Ree.LargeReeInvolutionComponentFree
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeModel
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentL5Orth
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19TabL5Key
public import CFSG.Quasithin.Background.E6EighteenF

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog Equiv

theorem g2_not_hasA7Component
    {k : Type} [Field k] [Finite k] {m : ℕ} (hm : 1 ≤ m)
    (hk : Nat.card k = 2 ^ m) : ¬ HasA7Component ↥(adjointGroup .G2 k) := by
  have : Finite ↥(adjointGroup .G2 k) := Subtype.finite
  rcases Nat.lt_or_ge 1 m with hm2 | hm1
  · have hsimple : IsSimpleGroup ↥(adjointGroup .G2 k) := by
      refine Id2519.isSimpleGroup_adjointGroup_g2 ?_
      rw [hk]
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    obtain ⟨-, h2, -⟩ := exact_G2_finite_order k (q := 2 ^ m) hk
    have hc2 : Nat.card ↥(adjointGroup .G2 k) =
        2 ^ (6 * m) * (((2 ^ m) ^ 6 - 1) * ((2 ^ m) ^ 2 - 1)) := by
      rw [h2]
      ring
    refine not_hasA7Component_of_isSimpleGroup ?_
    rw [hc2]
    exact two_pow_mul_ne_2520 (by omega)
  · have hm1' : m = 1 := le_antisymm hm1 hm
    have hk2 : Nat.card k = 2 := by rw [hk, hm1', pow_one]
    obtain ⟨hDsimple, hDcard⟩ := Id2519.g2Two_derived hk2
    have := hDsimple
    exact not_hasA7Component_of_commutator_simple (by rw [hDcard]; norm_num)

theorem noA7Fix_g2
    {Γ : Type} [Group Γ] {f : ℕ} (hf2 : 2 ≤ f)
    (hmodel : ChevalleyExceptionalModel Γ .G2 2 f) : NoA7Fix Γ := by
  intro a ha ha1' h0
  obtain ⟨-, F, _, _, hF, ⟨e₀⟩⟩ := hmodel
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := by
    have : Fintype F := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hF])
  have hZ : Subgroup.center ↥(adjointGroup .G2 F) = ⊥ := center_adjointGroup_eq_bot
  let e : Γ ≃* ↥(adjointGroup .G2 F) :=
    e₀.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)
  obtain ⟨α, hαdef⟩ : ∃ α : MulAut ↥(adjointGroup .G2 F), α = MulAut.congr e a := ⟨_, rfl⟩
  have hαα : α * α = 1 := by rw [hαdef, ← map_mul, ha, map_one]
  have h1 : HasA7Component ↥(Id2519.fixSubgroup α) := by
    rw [hαdef]
    exact hasA7Component_fixSubgroup_of_intertwine e a _
      (Id2519.mulAut_congr_apply_self e a) h0
  have hα1 : α ≠ 1 := fun h => ha1' ((MulAut.congr e).injective (by rw [← hαdef, h, map_one]))
  have hα2 : orderOf α = 2 := orderOf_eq_prime (by rwa [pow_two]) hα1
  rcases even_G2_involution_inner_or_canonical_field hf2 F hF α hα2 with hin | ⟨hev, hδ⟩
  · exact not_hasA7Component_fix_of_inner hZ
      (fun y hy B => Id2519.rootWeightDatum_involution_centralizer_component_free
        (RootWeightDatum.ordinary (K := F) .G2) y hy B) hαα hα1 hin h1
  · obtain ⟨m, hm⟩ := hev
    have hm1 : 1 ≤ m := by omega
    obtain ⟨φ₀, hφ₀, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
        Nat.prime_two (by omega) hF
    have hσ : ∀ c, (φ₀ ^ m) c = c ^ 2 ^ m :=
      CFSG.LocalAnalysis.ComponentInitial.ringAut_pow_apply_of_sq hφ₀ m
    obtain ⟨β, ψ, hβ, hψ, -⟩ := hδ (φ₀ ^ m).toRingHom fun c => by
      rw [show f / 2 = m by omega]
      exact hσ c
    have hβδ : β = entrywiseAdjointAut .G2 (φ₀ ^ m) :=
      MulEquiv.ext fun u => Subtype.ext (by rw [hβ u, coe_entrywiseAdjointAut])
    have hK2 : Nat.card F = 2 ^ (2 * m) := by rw [hF, show f = 2 * m by omega]
    obtain ⟨-, hk, -, hFix, -⟩ := even_G2_canonical_field_full_centralizer hm1 F hK2 (φ₀ ^ m) hσ
    have hint : ∀ y, β (ψ y) = ψ (α y) := fun y => by
      rw [← hψ, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
    have h2 : HasA7Component ↥(Id2519.fixSubgroup β) :=
      hasA7Component_fixSubgroup_of_intertwine ψ α β hint h1
    rw [hβδ] at h2
    have e₁ : ↥(adjointGroup .G2 (fixSubfield (φ₀ ^ m))) ≃*
        ↥(fixedFieldImage .G2 (φ₀ ^ m)) :=
      (adjointGroup .G2 (fixSubfield (φ₀ ^ m))).equivMapOfInjective _ (baseChangeGL_injective _)
    have e₂ : ↥(Id2519.fixSubgroup (entrywiseAdjointAut .G2 (φ₀ ^ m))) ≃*
        ↥(adjointGroup .G2 (fixSubfield (φ₀ ^ m))) :=
      (((Id2519.fixSubgroup (entrywiseAdjointAut .G2 (φ₀ ^ m))).equivMapOfInjective
        (adjointGroup .G2 F).subtype (adjointGroup .G2 F).subtype_injective).trans
        (MulEquiv.subgroupCongr hFix)).trans e₁.symm
    have : Finite (fixSubfield (φ₀ ^ m)) := Subtype.finite
    exact g2_not_hasA7Component hm1 hk (h2.of_mulEquiv e₂)

theorem trialityD4_not_hasA7Component
    {k : Type} [Field k] [Finite k] {m : ℕ} (hm : 1 ≤ m)
    (hk : Nat.card k = (2 ^ m) ^ 3) {r : ℕ} (hr : r = 1 ∨ r = 2) (σ₀ : k ≃+* k)
    (hσ₀ : ∀ c, σ₀ c = c ^ ((2 ^ m) ^ r)) (hσ₀3 : σ₀ ^ 3 = 1) :
    ¬ HasA7Component ↥(graphFixedRootGroup TwistTag.D4 k σ₀.toRingHom) := by
  have : Finite ↥(graphFixedRootGroup TwistTag.D4 k σ₀.toRingHom) := Subtype.finite
  have hk' : Nat.card k = 2 ^ (3 * m) := by rw [hk, ← pow_mul, mul_comm]
  have : CharP k 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hk'
  have h4 : 4 ≤ Nat.card k := by
    rw [hk']
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (3 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hperf := commutator_graphFixedRootGroup_triality_char_two (ringChar.eq k 2) σ₀
    (fun c => by
      have := congrArg (fun φ : k ≃+* k => φ c) hσ₀3
      simpa [pow_succ] using this) h4
  have hsimple := (isSimpleGroup_graphFixedRootGroup_of_perfect TwistTag.D4 k σ₀ hperf).1
  obtain ⟨hcard, -, -⟩ := triality_both_orientations_exact_finite_order 2 m Nat.prime_two hm k hk r
    hr σ₀.toRingHom hσ₀
  have hc2 : Nat.card ↥(graphFixedRootGroup TwistTag.D4 k σ₀.toRingHom) =
      2 ^ (12 * m) * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 6 - 1) *
        ((2 ^ m) ^ 8 + (2 ^ m) ^ 4 + 1)) := by
    rw [hcard]
    ring
  refine not_hasA7Component_of_isSimpleGroup ?_
  rw [hc2]
  exact two_pow_mul_ne_2520 (by omega)

theorem noA7Fix_trialityD4
    {Γ : Type} [Group Γ] {f : ℕ} (hf1 : 1 ≤ f)
    (hmodel : ChevalleyExceptionalModel Γ .trialityD4 2 f) : NoA7Fix Γ := by
  intro a ha ha1' h0
  obtain ⟨F, _, _, _, σ, hσ3, hσ, hFcard, -, ⟨e⟩⟩ :=
    TrialityCover.triality_model hf1 hmodel.2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 F σ.toRingHom) = ⊥ :=
    exceptional_fixed_center_trivial TwistTag.D4 F σ
  obtain ⟨α, hαdef⟩ : ∃ α : MulAut ↥(graphFixedRootGroup TwistTag.D4 F σ.toRingHom),
      α = MulAut.congr e a := ⟨_, rfl⟩
  have hαα : α * α = 1 := by rw [hαdef, ← map_mul, ha, map_one]
  have h1 : HasA7Component ↥(Id2519.fixSubgroup α) := by
    rw [hαdef]
    exact hasA7Component_fixSubgroup_of_intertwine e a _
      (Id2519.mulAut_congr_apply_self e a) h0
  have hα1 : α ≠ 1 := fun h => ha1' ((MulAut.congr e).injective (by rw [← hαdef, h, map_one]))
  by_cases hin : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
      ↥(graphFixedRootGroup TwistTag.D4 F σ.toRingHom)
  · exact not_hasA7Component_fix_of_inner hZ
      (fun y hy B => Id2519.rootWeightDatum_involution_centralizer_component_free
        (RootWeightDatum.fixed TwistTag.D4 σ hσ3) y hy B) hαα hα1 hin h1
  · have hα2' : α ^ 2 = 1 := by rw [pow_two]; exact hαα
    obtain ⟨hev, δ, hδ, -, ψ, hψ, -⟩ :=
      even_triality_outer_involutions_canonical_field hf1 F hFcard σ hσ α hα2' hin
    obtain ⟨m, hm⟩ := hev
    have hm1 : 1 ≤ m := by omega
    have hfm : f = 2 * m := by omega
    have hFcard' : Nat.card F = 2 ^ (6 * m) := by
      rw [hFcard, hfm]
      ring
    have hσ' : ∀ c, σ c = c ^ 2 ^ (2 * m) := fun c => by rw [hσ c, hfm]
    have hδ' : ∀ c, δ c = c ^ 2 ^ (3 * m) := fun c => by
      rw [hδ c, show 3 * f / 2 = 3 * m by omega]
    obtain ⟨-, hk0, hres, hord3, -, hFix, -⟩ :=
      even_triality_canonical_field_full_centralizer hm1 F hFcard' σ hσ' δ hδ'
    have hint : ∀ y, fieldActor σ δ (ψ y) = ψ (α y) := fun y => by
      rw [← hψ, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
    have h2 : HasA7Component ↥(Id2519.fixSubgroup (fieldActor σ δ)) :=
      hasA7Component_fixSubgroup_of_intertwine ψ α _ hint h1
    have e₁ : ↥(graphFixedRootGroup TwistTag.D4 (fixSubfield δ)
        (fixSubfieldRestrict σ δ).toRingHom) ≃* ↥(trialityFieldImage σ δ) :=
      (graphFixedRootGroup TwistTag.D4 (fixSubfield δ)
        (fixSubfieldRestrict σ δ).toRingHom).equivMapOfInjective _ (baseChangeGL_injective _)
    have e₂ : ↥(Id2519.fixSubgroup (fieldActor σ δ)) ≃*
        ↥(graphFixedRootGroup TwistTag.D4 (fixSubfield δ) (fixSubfieldRestrict σ δ).toRingHom) :=
      (((Id2519.fixSubgroup (fieldActor σ δ)).equivMapOfInjective
        (graphFixedRootGroup TwistTag.D4 F σ.toRingHom).subtype
        (graphFixedRootGroup TwistTag.D4 F σ.toRingHom).subtype_injective).trans
        (MulEquiv.subgroupCongr hFix)).trans e₁.symm
    have : Finite (fixSubfield δ) := Subtype.finite
    refine trialityD4_not_hasA7Component hm1 (by rw [hk0, pow_mul']) (Or.inr rfl)
      (fixSubfieldRestrict σ δ) (fun c => Subtype.ext ?_) ?_ (h2.of_mulEquiv e₂)
    · have hsq : (2 ^ m) ^ 2 = 2 ^ (2 * m) := by ring
      rw [hres c, hσ' (c : F), SubmonoidClass.coe_pow, hsq]
    · have := pow_orderOf_eq_one (fixSubfieldRestrict σ δ)
      rwa [hord3] at this

section Ree

open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution

theorem noA7Fix_twistedF4
    {X : Type} [Group X] [IsSimpleGroup X] {a b : X} (hab : a * b ≠ b * a) {f : ℕ}
    (hmodel : ReeTitsModel X .twistedF4 2 f) : NoA7Fix X := by
  intro α hα hne
  have hZ : Subgroup.center X = ⊥ := Id2519.center_eq_bot_of_simple_nonab ⟨a, b, hab⟩
  obtain ⟨-, hf3, -, -, -, hinner, hiso⟩ :=
    large_Ree_model_field_outer_group_and_inner_involutions X 2 f hmodel
  obtain ⟨-, m, hfm, hmodel'⟩ := hmodel
  obtain ⟨F, _, _, hF, ⟨e₀⟩⟩ := hmodel'
  have : Fintype F := Fintype.ofFinite F
  have : CharP F F4.prime := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hF]
    rfl)
  obtain ⟨⟨E⟩, -⟩ := hiso m F hfm hF ⟨e₀⟩
  have hF' : Nat.card F = 2 ^ (2 * m + 1) := hfm ▸ hF
  have hm : 1 ≤ m := by omega
  refine not_hasA7Component_fix_of_inner hZ (fun y hy B hB => ?_) hα hne
    (hinner α (by rw [pow_two]; exact hα))
  obtain ⟨B', hB'⟩ := Id2519.exists_isComponent_centralizer_of_mulEquiv E y hB
  have hy' : orderOf (E y) = 2 := by rw [MulEquiv.orderOf_eq]; exact hy
  exact (large_Ree_involution_centralizers_component_free m hm F hF').1 (E y) hy' B' hB'

end Ree

theorem noA7Fix_tits
    {X : Type} [Group X] [Finite X] (hmodel : ReeTitsModel X .Tits 2 1) : NoA7Fix X := by
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv X 2 1 hmodel
  refine noA7Fix_of_not_dvd ?_
  rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Schreier.Tits.card_titsD]
  norm_num

theorem noA7Fix_alt8 : NoA7Fix (alternatingGroup (Fin 8)) := by
  intro α hα hne hA
  obtain ⟨B, -, hB⟩ := hA
  obtain ⟨σ, hσ⟩ := CFSG.AlternatingAutomorphism.exists_perm_conj_of_degree_eq_five_or_seven_le
    (n := 8) (Or.inr (by norm_num)) α
  have hc := CFSG.ComponentClassification.PresentationLocal.centralizer_alternatingGroup_eq_bot
    (α := Fin 8) (by simp)
  have hsq : σ * σ = 1 := by
    have hmem : σ * σ ∈ Subgroup.centralizer (alternatingGroup (Fin 8) : Set (Perm (Fin 8))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have h2 := hσ (α ⟨g, hg⟩)
      have h3 : α (α ⟨g, hg⟩) = ⟨g, hg⟩ := by rw [← MulAut.mul_apply, hα, MulAut.one_apply]
      rw [h3, hσ ⟨g, hg⟩] at h2
      have h4 : g = σ * (σ * g * σ⁻¹) * σ⁻¹ := h2
      calc g * (σ * σ) = (σ * (σ * g * σ⁻¹) * σ⁻¹) * (σ * σ) := by rw [← h4]
        _ = σ * σ * g := by group
    rw [hc, Subgroup.mem_bot] at hmem
    exact hmem
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    apply hne
    refine MulEquiv.ext fun g => ?_
    rw [MulAut.one_apply]
    apply Subtype.ext
    have := hσ g
    rwa [one_mul, inv_one, mul_one] at this
  obtain ⟨k, hk1, hcyc⟩ := Id2519.involution_cycleType hsq hσ1
  have hk4 : k ≤ 4 := by
    have := Id2519.two_mul_le_of_cycleType hcyc
    omega
  have hcard := Id2519.card_centralizer_involution hk1 hcyc
  set B' : Subgroup (Perm (Fin 8)) :=
    (B.map (Id2519.fixSubgroup α).subtype).map (alternatingGroup (Fin 8)).subtype with hB'def
  have hB'C : B' ≤ Subgroup.centralizer ({σ} : Set (Perm (Fin 8))) := by
    rintro _ ⟨_, ⟨y, -, rfl⟩, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hfix : α (y : alternatingGroup (Fin 8)) = y := y.2
    have h := hσ (y : alternatingGroup (Fin 8))
    rw [hfix] at h
    change ((y : alternatingGroup (Fin 8)) : Perm (Fin 8)) * σ =
      σ * ((y : alternatingGroup (Fin 8)) : Perm (Fin 8))
    calc ((y : alternatingGroup (Fin 8)) : Perm (Fin 8)) * σ =
        (σ * ((y : alternatingGroup (Fin 8)) : Perm (Fin 8)) * σ⁻¹) * σ := by rw [← h]
      _ = σ * ((y : alternatingGroup (Fin 8)) : Perm (Fin 8)) := by group
  have hB'card : Nat.card ↥B' = Nat.card ↥B := by
    rw [hB'def, Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  have h7 : 7 ∣ Nat.card (Subgroup.centralizer ({σ} : Set (Perm (Fin 8)))) :=
    ((show 7 ∣ 2520 by norm_num).trans hB.dvd_card).trans
      (hB'card ▸ Subgroup.card_dvd_of_le hB'C)
  rw [hcard] at h7
  interval_cases k <;> norm_num [Nat.factorial] at h7

theorem noA7Fix_psl4_two {X : Type} [Group X]
    (hmodel : Assembly.LowTwoRank.StatedClassicalModel X .PSL 4 2 1) : NoA7Fix X := by
  obtain ⟨φ⟩ := (CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff
    X).mp (Or.inl ⟨by decide, hmodel⟩)
  exact NoA7Fix.of_mulEquiv φ.symm noA7Fix_alt8

theorem l5_card_fix_dvd {α : MulAut Id2519.Tab.L5.S} (a : Id2519.Tab.L5.S)
    (hα : α = MulAut.conj a * Id2519.Tab.L5.dl) (hαα : α * α = 1) :
    Nat.card ↥(Id2519.fixSubgroup α) ∣ 720 := by
  have hα2 : (MulAut.conj a * Id2519.Tab.L5.dl) * (MulAut.conj a * Id2519.Tab.L5.dl) = 1 := by
    rw [← hα]
    exact hαα
  have hsym : (a : Id2519.Tab.L5.M5).transpose = a := Id2519.Tab.L5.symm_of_sq a hα2
  set c : Id2519.Tab.L5.M5 := ((a⁻¹ : Id2519.Tab.L5.S) : Id2519.Tab.L5.M5) with hc
  have hcsym : c.transpose = c := by
    rw [hc, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_transpose, hsym]
  have hcdet : c.det ≠ 0 := by
    rw [hc, (a⁻¹ : Id2519.Tab.L5.S).2]
    exact one_ne_zero
  have hform : ∀ g ∈ Id2519.fixSubgroup α, (g : Id2519.Tab.L5.M5).transpose * c * g = c := by
    intro g hg
    have hfix : α g = g := hg
    rw [hα, MulAut.mul_apply, MulAut.conj_apply] at hfix
    have h1 : Id2519.Tab.L5.dl g = a⁻¹ * g * a := by
      calc Id2519.Tab.L5.dl g = a⁻¹ * (a * Id2519.Tab.L5.dl g * a⁻¹) * a := by group
        _ = a⁻¹ * g * a := by rw [hfix]
    have h2 : g.transpose = a⁻¹ * g⁻¹ * a := by
      rw [← Id2519.Tab.L5.dl_inv, h1]
      group
    have h3 : g.transpose * a⁻¹ * g = a⁻¹ := by
      calc g.transpose * a⁻¹ * g = (a⁻¹ * g⁻¹ * a) * a⁻¹ * g := by rw [h2]
        _ = a⁻¹ := by group
    have h4 := congrArg (fun z : Id2519.Tab.L5.S => (z : Id2519.Tab.L5.M5)) h3
    simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_transpose]
      using h4
  exact Id2519.Tab.L5.Orth.card_dvd_of_form hcsym hcdet _ hform

theorem noA7Fix_psl5_two {X : Type} [Group X] [IsSimpleGroup X] {a b : X} (hab : a * b ≠ b * a)
    (hmodel : Assembly.LowTwoRank.StatedClassicalModel X .PSL 5 2 1) : NoA7Fix X := by
  obtain ⟨-, F, hF, hFfin, hcard, ⟨e⟩⟩ := hmodel
  have hcard2 : Nat.card F = 2 := by simpa using hcard
  let φ : X ≃* Id2519.Tab.L5.S :=
    e.trans (CFSG.QuasithinUnique.Setup.Family.statedProjSL_equiv_of_card_two 5 F hcard2)
  have hZS : Subgroup.center Id2519.Tab.L5.S = ⊥ :=
    center_eq_bot_of_mulEquiv φ (Id2519.center_eq_bot_of_simple_nonab ⟨a, b, hab⟩)
  refine NoA7Fix.of_mulEquiv φ.symm ?_
  intro β hβ hne hA
  obtain ⟨c, ε, hε, hβeq⟩ := Id2519.Tab.L5.aut_form β
  interval_cases ε
  · simp only [pow_zero, mul_one] at hβeq
    exact not_hasA7Component_fix_of_inner hZS
      (fun y hy B => Id2519.Tab.L5.involution_centralizer_component_free hy B) hβ hne
      ⟨c, hβeq.symm⟩ hA
  · simp only [pow_one] at hβeq
    obtain ⟨B, -, hB⟩ := hA
    have h := (hB.dvd_card.trans (Subgroup.card_subgroup_dvd_card B)).trans
      (l5_card_fix_dvd c hβeq hβ)
    norm_num at h

theorem noA7Fix_sqtkCharTwoLie
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {a b : X} (hab : a * b ≠ b * a)
    (h : SQTKCharTwoLie X) : NoA7Fix X := by
  rcases h with (⟨f, h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8⟩ | h9) | ⟨n, hn, h10⟩
  · exact noA7Fix_psl2_even (by omega) h1.2
  · obtain ⟨hf, hm⟩ := h2
    rcases Nat.lt_or_ge f 3 with hf3 | hf3
    · interval_cases f
      · exact noA7Fix_psl3_two hm
      · exact noA7Fix_psl3_four hm
    · exact noA7Fix_psl3_even hf3 hm hab
  · exact noA7Fix_psu3_even h3.1 h3.2 hab
  · exact noA7Fix_psp4_even h4.1 h4.2 hab
  · exact noA7Fix_g2 h5.1 h5.2
  · exact noA7Fix_trialityD4 h6.1 h6.2
  · exact noA7Fix_twistedF4 hab h7.2.2
  · exact noA7Fix_suzuki h8.2.2
  · exact noA7Fix_tits h9
  · rcases hn with rfl | rfl
    · exact noA7Fix_psl4_two h10
    · exact noA7Fix_psl5_two hab h10

end E6

end CFSG.Quasithin
