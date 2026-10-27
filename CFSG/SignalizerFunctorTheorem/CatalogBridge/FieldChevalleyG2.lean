module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldAutNL
import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldChevalleyEven
import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldChevalleyOdd
import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldChevalleyE
import CFSG.RankThree.SteinbergBRThreeG2Noninner
import CFSG.RankThree.Chevalley.EvenRealThreeCentralizingInvolution
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieG2
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField

public section

open CFSG.Open (signalizerFixedSubgroup signalizerNearPSolvable)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Ree (ReeTag)
open CFSG.RankThree.Chevalley.SteinbergBT (orderOf_entrywiseAdjointAut not_commute_fixedFieldImage
  card_fixSubfield pow_card_eq_self_of_mem)
open CFSG.ComponentClassification.UnbalancedCatalog (ringAut_commute mem_zpowers_of_fixed
  entrywiseFixedGroup_eq_fixedFieldImage even_G2_exact_automorphism_normal_form
  entrywise_baseChangeGL_restrict units_map_entrywise_refl_k ringEquiv_eq_refl_of_card_two)
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic
  finite_field_automorphism_fixed_field_cardinality)
open CFSG.RankThree.Chevalley (exists_mulEquiv_adjointGroup_of_untwisted
  three_G2_subfield_normalizer_and_pointwise_automorphism_centralizer)
open CFSG.RankThree (three_G2_noninner_odd_prime_local_core_trivial)
open CFSG.QuasithinUnique.Id2519 (isSimpleGroup_adjointGroup_g2 g2Two_derived)
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem isSimpleGroup_fixedFieldImage_G2
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hk : 3 ≤ Nat.card (fixSubfield σ)) : IsSimpleGroup (fixedFieldImage .G2 σ) := by
  have : IsSimpleGroup (adjointGroup .G2 (fixSubfield σ)) := isSimpleGroup_adjointGroup_g2 hk
  exact (fixedFieldImageEquiv (τ := .G2) σ).symm.isSimpleGroup

theorem g2Two_derived_nonabelian
    {k : Type} [Field k] [Finite k] (hk : Nat.card k = 2) :
    ∃ a b : ↥(commutator ↥(adjointGroup .G2 k)), a * b ≠ b * a := by
  obtain ⟨hs, hcard⟩ := g2Two_derived hk
  by_contra hcon
  push Not at hcon
  have : IsSimpleGroup ↥(commutator ↥(adjointGroup .G2 k)) := hs
  let _ : CommGroup ↥(commutator ↥(adjointGroup .G2 k)) :=
    { (inferInstance : Group ↥(commutator ↥(adjointGroup .G2 k))) with mul_comm := hcon }
  have hp := IsSimpleGroup.prime_card (α := ↥(commutator ↥(adjointGroup .G2 k)))
  rw [hcard] at hp
  exact absurd hp (by norm_num)

theorem nonempty_mulEquiv_fixedGroup_G2
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K) :
    Nonempty (signalizerFixedSubgroup (entrywiseAdjointAut .G2 σ) ≃*
      adjointGroup .G2 (fixSubfield σ)) := by
  classical
  have hΓJ := entrywiseFixedGroup_eq_fixedFieldImage σ
  have hmemN : ∀ g : adjointGroup .G2 K,
      g ∈ signalizerFixedSubgroup (entrywiseAdjointAut .G2 σ) ↔
        (g : ModGL .G2 K) ∈ fixedFieldImage .G2 σ := by
    intro g
    rw [← hΓJ, mem_entrywiseFixedGroup]
    constructor
    · intro h
      exact ⟨g.2, congrArg Subtype.val (show entrywiseAdjointAut .G2 σ g = g from h)⟩
    · rintro ⟨-, h⟩
      exact Subtype.ext h
  have hmap : (signalizerFixedSubgroup (entrywiseAdjointAut .G2 σ)).map
      (adjointGroup .G2 K).subtype = fixedFieldImage .G2 σ := by
    ext y
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact (hmemN g).1 hg
    · intro hy
      have hyC : y ∈ adjointGroup .G2 K := ((mem_entrywiseFixedGroup).1 (hΓJ ▸ hy)).1
      exact ⟨⟨y, hyC⟩, (hmemN ⟨y, hyC⟩).2 hy, rfl⟩
  exact ⟨((signalizerFixedSubgroup (entrywiseAdjointAut .G2 σ)).equivMapOfInjective
    (adjointGroup .G2 K).subtype (adjointGroup .G2 K).subtype_injective).trans
    ((MulEquiv.subgroupCongr hmap).trans (fixedFieldImageEquiv (τ := .G2) σ).symm)⟩

theorem fStarSimple_fixed_evenG2
    {K : Type} [Field K] [Finite K] {d : ℕ} (hd : 1 ≤ d)
    (σ : K ≃+* K) (hk : Nat.card (fixSubfield σ) = 2 ^ d) :
    FStarSimple (signalizerFixedSubgroup (entrywiseAdjointAut .G2 σ)) := by
  classical
  obtain ⟨e⟩ := nonempty_mulEquiv_fixedGroup_G2 σ
  have : Finite (fixSubfield σ) := Subtype.finite
  have : Finite (ModGL .G2 (fixSubfield σ)) := finite_modGL
  rcases Nat.lt_or_ge 1 d with hd2 | hd1
  ·
    have hk3 : 3 ≤ Nat.card (fixSubfield σ) := by
      rw [hk]
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd2
    have : IsSimpleGroup (adjointGroup .G2 (fixSubfield σ)) := isSimpleGroup_adjointGroup_g2 hk3
    have hnk : ∃ a b : adjointGroup .G2 (fixSubfield σ), a * b ≠ b * a := by
      by_contra hcon
      push Not at hcon
      apply not_commute_fixedFieldImage (τ := .G2) (by decide) σ
      intro a b
      have h := hcon ((fixedFieldImageEquiv (τ := .G2) σ).symm a)
        ((fixedFieldImageEquiv (τ := .G2) σ).symm b)
      apply (fixedFieldImageEquiv (τ := .G2) σ).symm.injective
      rw [map_mul, map_mul]
      exact h
    refine fStarSimple_of_simple e.isSimpleGroup ?_
    obtain ⟨a, b, hab⟩ := hnk
    exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by simpa using h))⟩
  ·
    have hk2 : Nat.card (fixSubfield σ) = 2 := by rw [hk, le_antisymm hd1 hd, pow_one]
    obtain ⟨hDs, -⟩ := g2Two_derived hk2
    have hFk := isFStarSimple_of_derived_simple center_adjointGroup_eq_bot hDs
      (g2Two_derived_nonabelian hk2)
    exact (fStarSimple_iff_isFStarSimple _).mpr
      ((McBride.Nonsolv.L514.isFStarSimple_congr e.symm).1 hFk)

theorem threeG2_zpowers_of_fixes
    {f d : ℕ} (hf : 1 ≤ f) (hd : 1 ≤ d) (hdf : d ∣ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = 3 ^ f) (σ : K ≃+* K)
    (hkcard : Nat.card (fixSubfield σ) = 3 ^ d) :
    ∀ β : MulAut (adjointGroup .G2 K),
      (∀ j : adjointGroup .G2 K, (j : ModGL .G2 K) ∈ fixedFieldImage .G2 σ → β j = j) →
        β ∈ Subgroup.zpowers (entrywiseAdjointAut .G2 σ) := by
  classical
  have : CharP K ReeTag.G2.prime := finite_field_prime_power_characteristic Nat.prime_three hf hK
  obtain ⟨-, -, hfixing, -, -⟩ :=
    three_G2_subfield_normalizer_and_pointwise_automorphism_centralizer hf hd hdf hK
      (fixSubfield σ) hkcard
  intro β hβ
  let β' : MulAut (adjointGroup ReeTag.G2.tag K) := β
  have hβ' : ∀ y : adjointGroup ReeTag.G2.tag K,
      (y : ModGL ReeTag.G2.tag K) ∈ fixedFieldImage ReeTag.G2.tag σ → β' y = y := hβ
  have hβmem : β' ∈ Subgroup.zpowers (ReeTag.G2.finiteFrobeniusAut K ^ d) := by
    rw [← hfixing]
    refine (mem_fixingSubgroup_iff _).2 fun y hy => ?_
    rw [MulAut.smul_def]
    exact hβ' y (Subgroup.mem_subgroupOf.1 hy)
  obtain ⟨fr, hfr, -⟩ := finite_field_automorphism_fixed_field_cardinality Nat.prime_three hf hK
  have hT : ∀ c, (fr ^ d) c = c ^ 3 ^ d := ringAut_pow_apply_of_frobenius hfr d
  have hFr : ReeTag.G2.finiteFrobeniusAut K ^ d = entrywiseAdjointAut ReeTag.G2.tag (fr ^ d) := by
    rw [← exactNormalAut_one_eq_finiteFrobeniusAut_pow ReeTag.G2 (σ := fr ^ d) (j := d) hT,
      FieldGraphFieldPointwise.exactNormalAut_one_zero_eq]
  have hTσ : fr ^ d ∈ Subgroup.zpowers σ := mem_zpowers_of_fixed fun c hc => by
    rw [hT]
    exact pow_card_eq_self_of_mem (k := fixSubfield σ) hkcard hc
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hTσ
  have hFrmem : ReeTag.G2.finiteFrobeniusAut K ^ d ∈
      Subgroup.zpowers (entrywiseAdjointAut .G2 σ) := by
    rw [hFr, ← hn]
    exact Subgroup.mem_zpowers_iff.2 ⟨n, (map_zpow (entrywiseAdjointAutHom (τ := .G2)) σ n).symm⟩
  exact Subgroup.zpowers_le.2 hFrmem hβmem

theorem fieldClauses_threeG2
    {f p : ℕ} (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = 3 ^ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hsC : IsSimpleGroup (adjointGroup .G2 K)) (hnC : ∃ a b : adjointGroup .G2 K, a * b ≠ b * a)
    (hpC : ¬ p ∣ Nat.card (adjointGroup .G2 K)) (hNL : ChevalleySubfieldNL .G2 K p) :
    FieldClauses p (adjointGroup .G2 K) := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : Finite (ModGL .G2 K) := finite_modGL
  have : CharP K ReeTag.G2.prime := finite_field_prime_power_characteristic Nat.prime_three hf hK
  rintro ⟨α, hα⟩
  have hout := not_mem_inner_range_of_orderOf hpC hα
  have hB : orderOf (⟨α, Subgroup.mem_top α⟩ :
      (⊤ : Subgroup (MulAut (adjointGroup .G2 K)))) = p :=
    (Subgroup.orderOf_mk α (Subgroup.mem_top α)).trans hα
  obtain ⟨-, hNF, -⟩ := G2_three_exact_automorphism_normal_form hf K hK
  obtain ⟨⟨x, a⟩, hxa, -⟩ := hNF α
  have hxa' : α = MulAut.conj x * ReeTag.G2.finiteExceptionalAut K ^ (a : ℕ) := hxa
  obtain ⟨hpf, -, ⟨σ, -, hσ, -, -⟩, -⟩ :=
    three_G2_noninner_odd_prime_local_core_trivial hf hK hp hp2 ⊤ le_top ⟨α, Subgroup.mem_top α⟩
      hout hB x a a.isLt hxa'
  obtain ⟨-, hkcard⟩ := card_fixSubfield Nat.prime_three hf hK σ
  rw [hσ] at hkcard
  have hd1 : 1 ≤ f / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) hp.pos
  have hk3 : 3 ≤ Nat.card (fixSubfield σ) := by
    rw [hkcard]
    calc 3 = 3 ^ 1 := (pow_one 3).symm
      _ ≤ 3 ^ (f / p) := Nat.pow_le_pow_right (by norm_num) hd1
  have hord : orderOf (entrywiseAdjointAut .G2 σ) = p := by
    rw [orderOf_entrywiseAdjointAut (by decide) σ, hσ]
  exact ⟨entrywiseAdjointAut .G2 σ, hord, fixedClauses_of_J_simple_stabilizer hp hsC hnC hpC σ hσ
    (isSimpleGroup_fixedFieldImage_G2 σ hk3)
    (threeG2_zpowers_of_fixes hf hd1 (Nat.div_dvd_of_dvd hpf) K hK σ hkcard)
    fun _ => nonLocalized_fixed_entrywiseAdjointAut σ (hNL σ hσ)⟩

theorem fieldClauses_chevalleyThreeG2
    {T : Type} [Group T] [Finite T] (hs : IsSimpleGroup T)
    (hn : ∃ a b : T, a * b ≠ b * a) {ℓ f p : ℕ}
    (hm : CFSG.Blueprint.ChevalleyExceptionalModel T .G2 ℓ f) (hℓ3 : ℓ = 3) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpT : ¬ p ∣ Nat.card T) (hNL : SubfieldNonLocalizedChevalley) :
    FieldClauses p T := by
  subst hℓ3
  obtain ⟨hadm, hmod⟩ := hm
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_adjointGroup_of_untwisted hmod
  have : IsSimpleGroup T := hs
  have : Finite (adjointGroup .G2 K) := Finite.of_equiv T e.symm.toEquiv
  have hsC : IsSimpleGroup (adjointGroup .G2 K) := e.isSimpleGroup
  have hnC : ∃ a b : adjointGroup .G2 K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hn
    exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by simpa using h))⟩
  have hpC : ¬ p ∣ Nat.card (adjointGroup .G2 K) := by rwa [Nat.card_congr e.toEquiv]
  exact FieldClauses.of_mulEquiv e
    (fieldClauses_threeG2 hadm.2.1 K hK hp hp2 hsC hnC hpC
      (ChevalleySubfieldNL.of_chevalley hNL (Or.inl rfl) hsC hp hp2 hpC))

theorem eq_one_of_forall_fixedFieldImage_evenG2
    {d : ℕ} (hd : 1 ≤ d) {K : Type} [Field K]
    [Finite K] {σ : K ≃+* K} (hk : Nat.card (fixSubfield σ) = 2 ^ d) {g : adjointGroup .G2 K}
    (hgJ : (g : ModGL .G2 K) ∈ fixedFieldImage .G2 σ) (φ : K ≃+* K)
    (hfix : ∀ j : adjointGroup .G2 K, (j : ModGL .G2 K) ∈ fixedFieldImage .G2 σ →
      (g : ModGL .G2 K) * Units.map (entrywiseHom φ.toRingHom) (j : ModGL .G2 K) *
        (g : ModGL .G2 K)⁻¹ = j) :
    g = 1 ∧ ∀ c ∈ fixSubfield σ, φ c = c := by
  classical
  rcases Nat.lt_or_ge 1 d with hd2 | hd1
  ·
    obtain ⟨hNFk, -⟩ := even_G2_exact_automorphism_normal_form hd2 (fixSubfield σ) hk
    exact eq_one_of_forall_fixedFieldImage_of_normalForm hNFk hgJ φ hfix
  ·
    have hk2 : Nat.card (fixSubfield σ) = 2 := by rw [hk, le_antisymm hd1 hd, pow_one]
    set k := fixSubfield σ
    have : Finite k := Subtype.finite
    set ι := baseChangeGL (τ := .G2) k.subtype
    have hιinj : Function.Injective ι := baseChangeGL_injective _
    obtain ⟨g', hg', hgg'⟩ := hgJ
    set ψ := fixSubfieldRestrict φ σ
    have hid : ∀ j' ∈ adjointGroup .G2 k,
        g' * Units.map (entrywiseHom ψ.toRingHom) j' * g'⁻¹ = j' := by
      intro j' hj'
      have hj'J : ι j' ∈ fixedFieldImage .G2 σ := ⟨j', hj', rfl⟩
      have hj'C : ι j' ∈ adjointGroup .G2 K := fixedFieldImage_le hj'J |>.1
      have h1 := hfix ⟨ι j', hj'C⟩ hj'J
      change (g : ModGL .G2 K) * Units.map (entrywiseHom φ.toRingHom) (ι j') *
        (g : ModGL .G2 K)⁻¹ = ι j' at h1
      rw [← hgg', entrywise_baseChangeGL_restrict, ← map_inv, ← map_mul, ← map_mul] at h1
      exact hιinj h1
    have hψ1 := ringEquiv_eq_refl_of_card_two hk2 ψ
    have hg'1 : g' = 1 := by
      have hZ : Subgroup.center (adjointGroup .G2 k) = ⊥ := center_adjointGroup_eq_bot
      have hc : (⟨g', hg'⟩ : adjointGroup .G2 k) ∈ Subgroup.center (adjointGroup .G2 k) := by
        refine Subgroup.mem_center_iff.2 fun j => Subtype.ext ?_
        have h1 := hid j j.2
        rw [hψ1, units_map_entrywise_refl_k] at h1
        change (j : ModGL .G2 k) * g' = g' * j
        rw [← mul_inv_eq_iff_eq_mul.1 h1]
      rw [hZ, Subgroup.mem_bot] at hc
      exact congrArg Subtype.val hc
    refine ⟨Subtype.ext ?_, fun c hc => ?_⟩
    · rw [← hgg', hg'1, map_one]
      rfl
    · have h1 := congrArg (fun ψ' : k ≃+* k => (ψ' ⟨c, hc⟩ : K)) hψ1
      simp only [ψ] at h1
      exact h1

theorem hS2_evenG2
    {f d : ℕ} (hf : 2 ≤ f) (hd : 1 ≤ d) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ f) (σ : K ≃+* K) (hk : Nat.card (fixSubfield σ) = 2 ^ d) :
    ∀ β : MulAut (adjointGroup .G2 K),
      β * entrywiseAdjointAut .G2 σ = entrywiseAdjointAut .G2 σ * β →
      (∀ j : adjointGroup .G2 K, (j : ModGL .G2 K) ∈ fixedFieldImage .G2 σ → β j = j) →
        β ∈ Subgroup.zpowers (entrywiseAdjointAut .G2 σ) := by
  classical
  intro β hβδ hβfix
  have hZ : Subgroup.center (adjointGroup .G2 K) = ⊥ := center_adjointGroup_eq_bot
  have hinj := mulAut_conj_injective_of_center_eq_bot hZ
  set δ := entrywiseAdjointAut .G2 σ with hδ
  have hΓJ := entrywiseFixedGroup_eq_fixedFieldImage σ
  have hmemJ : ∀ g : adjointGroup .G2 K,
      (g : ModGL .G2 K) ∈ fixedFieldImage .G2 σ ↔ δ g = g := by
    intro g
    rw [← hΓJ, mem_entrywiseFixedGroup]
    constructor
    · rintro ⟨-, h⟩
      exact Subtype.ext h
    · intro h
      exact ⟨g.2, congrArg Subtype.val h⟩
  obtain ⟨hNF, -⟩ := even_G2_exact_automorphism_normal_form hf K hK
  have hcommδ : ∀ φ : K ≃+* K, entrywiseAdjointAut .G2 φ * δ = δ * entrywiseAdjointAut .G2 φ :=
    fun φ => by rw [hδ, ← entrywiseAdjointAut_mul, ← entrywiseAdjointAut_mul, ringAut_commute]
  have hform : ∀ (β : MulAut (adjointGroup .G2 K)) (g : adjointGroup .G2 K) (φ : K ≃+* K),
      (∀ h : adjointGroup .G2 K, (β h : ModGL .G2 K) = (g : ModGL .G2 K) *
        Units.map (entrywiseHom φ.toRingHom) (h : ModGL .G2 K) * (g : ModGL .G2 K)⁻¹) →
      β = MulAut.conj g * entrywiseAdjointAut .G2 φ := fun β g φ h =>
    MulEquiv.ext fun x => Subtype.ext (by
      rw [h x, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        coe_entrywiseAdjointAut, Subgroup.coe_inv])
  obtain ⟨⟨g, φ⟩, hgφ, -⟩ := hNF β
  have hgJ : (g : ModGL .G2 K) ∈ fixedFieldImage .G2 σ := by
    have hβδ' : δ * β = β * δ := hβδ.symm
    rw [hform β g φ hgφ] at hβδ'
    have e1 : MulAut.conj (δ g) * (δ * entrywiseAdjointAut .G2 φ) =
        MulAut.conj g * (δ * entrywiseAdjointAut .G2 φ) := by
      calc MulAut.conj (δ g) * (δ * entrywiseAdjointAut .G2 φ) =
          δ * (MulAut.conj g * entrywiseAdjointAut .G2 φ) := by
            rw [← mul_assoc, ← mulAut_mul_conj, mul_assoc]
        _ = MulAut.conj g * entrywiseAdjointAut .G2 φ * δ := hβδ'
        _ = MulAut.conj g * (δ * entrywiseAdjointAut .G2 φ) := by rw [mul_assoc, hcommδ]
    exact (hmemJ g).2 (hinj (mul_right_cancel e1))
  have hfix : ∀ j : adjointGroup .G2 K, (j : ModGL .G2 K) ∈ fixedFieldImage .G2 σ →
      (g : ModGL .G2 K) * Units.map (entrywiseHom φ.toRingHom) (j : ModGL .G2 K) *
        (g : ModGL .G2 K)⁻¹ = j := fun j hj => by
    rw [← hgφ j, hβfix j hj]
  obtain ⟨hg1, hφk⟩ := eq_one_of_forall_fixedFieldImage_evenG2 hd hk hgJ φ hfix
  have hφ : φ ∈ Subgroup.zpowers σ := mem_zpowers_of_fixed fun x hx => hφk x hx
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hφ
  refine Subgroup.mem_zpowers_iff.2 ⟨n, ?_⟩
  rw [hform β g (σ ^ n) hgφ, hg1, map_one, one_mul, hδ]
  exact (map_zpow (entrywiseAdjointAutHom (τ := .G2)) σ n).symm

theorem exists_fieldAut_evenG2
    {f p : ℕ} (hf : 2 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = 2 ^ f) (hp : p.Prime) (hpC : ¬ p ∣ Nat.card (adjointGroup .G2 K))
    {α : MulAut (adjointGroup .G2 K)} (hα : orderOf α = p) : ∃ σ : K ≃+* K, orderOf σ = p := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : Finite (ModGL .G2 K) := finite_modGL
  obtain ⟨-, Θ, -, -, hΘker, -⟩ := even_G2_exact_automorphism_normal_form hf K hK
  have hσp : Θ α ^ p = 1 := by rw [← map_pow, ← hα, pow_orderOf_eq_one, map_one]
  have hσ1 : Θ α ≠ 1 := by
    intro h
    have hmem : α ∈ Θ.ker := h
    rw [hΘker] at hmem
    exact not_mem_inner_range_of_orderOf hpC hα hmem
  exact ⟨Θ α, orderOf_eq_prime hσp hσ1⟩

theorem fixedClauses_evenG2
    {f p : ℕ} (hf : 2 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = 2 ^ f) (hp : p.Prime) (σ : K ≃+* K) (hσ : orderOf σ = p)
    (hNL : FStarSimple (signalizerFixedSubgroup (entrywiseAdjointAut .G2 σ)) →
      NonLocalized (signalizerFixedSubgroup (entrywiseAdjointAut .G2 σ))) :
    FixedClauses p (signalizerFixedSubgroup (entrywiseAdjointAut .G2 σ)) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  obtain ⟨-, Θ, -, -, hΘker, -⟩ := even_G2_exact_automorphism_normal_form hf K hK
  obtain ⟨hpf, hkcard⟩ := card_fixSubfield Nat.prime_two (by omega) hK σ
  rw [hσ] at hpf hkcard
  have hd : 1 ≤ f / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpf) hp.pos
  exact fixedClauses_of_FStarSimple_S2 σ hσ (by decide) (entrywiseFixedGroup_eq_fixedFieldImage σ)
    (fStarSimple_fixed_evenG2 hd σ hkcard)
    (commutator_mem_inner_of_hom (fun a b => ringAut_commute a b) Θ hΘker)
    (hS2_evenG2 hf hd K hK σ hkcard) hNL

theorem fieldClauses_evenG2
    {f p : ℕ} (hf : 2 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = 2 ^ f) (hp : p.Prime) (hpC : ¬ p ∣ Nat.card (adjointGroup .G2 K))
    (hNL : ChevalleySubfieldNL .G2 K p) : FieldClauses p (adjointGroup .G2 K) := by
  rintro ⟨α, hα⟩
  obtain ⟨σ, hσ⟩ := exists_fieldAut_evenG2 hf K hK hp hpC hα
  have hf₀ : orderOf (entrywiseAdjointAut .G2 σ) = p := by
    rw [orderOf_entrywiseAdjointAut (by decide) σ, hσ]
  exact ⟨entrywiseAdjointAut .G2 σ, hf₀, fixedClauses_evenG2 hf K hK hp σ hσ
    fun _ => nonLocalized_fixed_entrywiseAdjointAut σ (hNL σ hσ)⟩

theorem fieldClauses_chevalleyEvenG2
    {T : Type} [Group T] [Finite T] (hs : IsSimpleGroup T)
    {ℓ f p : ℕ} (hm : CFSG.Blueprint.ChevalleyExceptionalModel T .G2 ℓ f) (hℓ2 : ℓ = 2)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpT : ¬ p ∣ Nat.card T)
    (hNL : SubfieldNonLocalizedChevalley) : FieldClauses p T := by
  subst hℓ2
  obtain ⟨hadm, hmod⟩ := hm
  have hf2 : 2 ≤ f := by
    have h3 : 3 ≤ 2 ^ f := hadm.2.2.2
    by_contra h
    have hf1 : f = 1 := by have := hadm.2.1; omega
    subst hf1
    norm_num at h3
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_adjointGroup_of_untwisted hmod
  have : IsSimpleGroup T := hs
  have : Finite (adjointGroup .G2 K) := Finite.of_equiv T e.symm.toEquiv
  have hsC : IsSimpleGroup (adjointGroup .G2 K) := e.isSimpleGroup
  have hpC : ¬ p ∣ Nat.card (adjointGroup .G2 K) := by rwa [Nat.card_congr e.toEquiv]
  exact FieldClauses.of_mulEquiv e
    (fieldClauses_evenG2 hf2 K hK hp hpC
      (ChevalleySubfieldNL.of_chevalley hNL (Or.inl rfl) hsC hp hp2 hpC))

theorem nearOrField_chevalleyG2
    {T : Type} [Group T] [Finite T] (hs : IsSimpleGroup T)
    (hn : ∃ a b : T, a * b ≠ b * a) {ℓ f p : ℕ}
    (hm : CFSG.Blueprint.ChevalleyExceptionalModel T .G2 ℓ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpT : ¬ p ∣ Nat.card T) (hNL : SubfieldNonLocalizedChevalley) :
    signalizerNearPSolvable p T ∨ FieldClauses p T := by
  refine Or.inr ?_
  by_cases h2 : ℓ = 2
  · exact fieldClauses_chevalleyEvenG2 hs hm h2 hp hp2 hpT hNL
  · by_cases h3 : ℓ = 3
    · exact fieldClauses_chevalleyThreeG2 hs hn hm h3 hp hp2 hpT hNL
    · exact fieldClauses_chevalleyOddG2 hs hm h2 h3 hp hp2 hpT hNL

end CFSG.SignalizerFunctorTheorem.CatalogBridge
