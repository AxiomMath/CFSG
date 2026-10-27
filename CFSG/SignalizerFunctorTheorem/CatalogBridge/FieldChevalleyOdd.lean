module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.StabilizerLift
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldAutNL
import CFSG.RankThree.Chevalley.SteinbergCFOddE8InnerField
import CFSG.RankThree.Chevalley.EvenRealThreeCentralizingInvolution

public section

open CFSG.Open (signalizerFixedSubgroup)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley.SteinbergBT (orderOf_entrywiseAdjointAut not_commute_fixedFieldImage)
open CFSG.ComponentClassification.UnbalancedCatalog (mem_zpowers_of_fixed)
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic)
open CFSG.RankThree.Chevalley (conj_normalForm_of_pointwise eq_of_conj_mul_entrywiseAdjointAut_eq
  exists_mulEquiv_adjointGroup_of_untwisted
  odd_E8_inner_field_automorphisms_and_noninner_prime_core)

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem odd_hfixer_of_normalForm
    {τ : Tag} {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2)
    {K : Type} [Field K] [Finite K] [CharP K ℓ]
    (hNF : ∀ η : MulAut (adjointGroup τ K), ∃ gβ : adjointGroup τ K × (K ≃+* K),
      η = MulAut.conj gβ.1 * entrywiseAdjointAut τ gβ.2) (σ : K ≃+* K) :
    ∀ β : MulAut (adjointGroup τ K),
      (∀ j : adjointGroup τ K, (j : ModGL τ K) ∈ fixedFieldImage τ σ → β j = j) →
        ∃ η : K ≃+* K, (∀ c, σ c = c → η c = c) ∧ β = entrywiseAdjointAut τ η := by
  classical
  intro β hfix
  have hJC : fixedFieldImage τ σ ≤ adjointGroup τ K := fun j hj => (fixedFieldImage_le hj).1
  set ι : ZMod ℓ →+* K := ZMod.castHom (dvd_refl ℓ) K
  set ιk : ZMod ℓ →+* fixSubfield σ := ZMod.castHom (dvd_refl ℓ) (fixSubfield σ)
  have hιk : ι = (fixSubfield σ).subtype.comp ιk := RingHom.ext_zmod _ _
  have hHJ : ∀ g0 ∈ adjointGroup τ (ZMod ℓ), baseChangeGL ι g0 ∈ fixedFieldImage τ σ :=
    fun g0 hg0 => ⟨baseChangeGL ιk g0, baseChangeGL_mem_adjointGroup ιk hg0, by
      rw [baseChangeGL_baseChangeGL, ← hιk]⟩
  have hodd : Odd (Nat.card (ZMod ℓ)) := by
    rw [Nat.card_zmod]
    exact (Fact.out : ℓ.Prime).odd_of_ne_two hℓ2
  have hfaith := (exceptional_Lang_finite_root_centralizer_faithfulness τ (ZMod ℓ) hodd K ι).2.2.1
  obtain ⟨⟨g, η⟩, hgη⟩ := hNF β
  simp only at hgη
  have hg1 : g = 1 := by
    refine Subtype.ext (hfaith g g.2 fun h hh => ?_)
    obtain ⟨g0, hg0, rfl⟩ := hh
    have hhJ := hHJ g0 hg0
    have h1 := congrArg Subtype.val (hfix ⟨_, hJC hhJ⟩ hhJ)
    rw [hgη, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      coe_entrywiseAdjointAut, Subgroup.coe_inv] at h1
    change (g : ModGL τ K) * Units.map (entrywiseHom η.toRingHom) (baseChangeGL ι g0) *
      (g : ModGL τ K)⁻¹ = baseChangeGL ι g0 at h1
    rw [units_map_entrywiseHom_eq_baseChangeGL, baseChangeGL_baseChangeGL,
      RingHom.ext_zmod (η.toRingHom.comp ι) ι] at h1
    exact mul_inv_eq_iff_eq_mul.1 h1
  subst hg1
  have hβη : β = entrywiseAdjointAut τ η := by rw [hgη, map_one, one_mul]
  refine ⟨η, fun c hc => ?_, hβη⟩
  have h1 := hfix (adjX τ K ⟨0, τ.rank_pos⟩ c) (xUnit_mem_fixedFieldImage _ hc)
  rw [hβη, FieldGraphFieldPointwise.entrywiseAdjointAut_adjX] at h1
  exact adjX_injective _ h1

theorem fixedClauses_odd_of_fixer
    {τ : Tag} {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2)
    {K : Type} [Field K] [Finite K] [CharP K ℓ] {p : ℕ} (hp : p.Prime)
    (hpC : ¬ p ∣ Nat.card (adjointGroup τ K)) (σ : K ≃+* K) (hσ : orderOf σ = p)
    (hfixer : ∀ β : MulAut (adjointGroup τ K),
      (∀ j : adjointGroup τ K, (j : ModGL τ K) ∈ fixedFieldImage τ σ → β j = j) →
        ∃ η : K ≃+* K, (∀ c, σ c = c → η c = c) ∧ β = entrywiseAdjointAut τ η)
    (hNL : FStarSimple (signalizerFixedSubgroup (entrywiseAdjointAut τ σ)) →
      NonLocalized (signalizerFixedSubgroup (entrywiseAdjointAut τ σ))) :
    FixedClauses p (signalizerFixedSubgroup (entrywiseAdjointAut τ σ)) := by
  classical
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  have : Finite (ModGL τ K) := finite_modGL
  obtain ⟨hsC, hnC, -⟩ := odd_pinned_Chevalley_p_components τ K hK2
  have hJΓ : fixedFieldImage τ σ ≤ entrywiseFixedGroup τ σ := fixedFieldImage_le
  have hJC : fixedFieldImage τ σ ≤ adjointGroup τ K := fun j hj => (hJΓ hj).1
  have hk2 : ringChar (fixSubfield σ) ≠ 2 := by
    intro h
    have h0 : ((2 : ℕ) : fixSubfield σ) = 0 := by
      rw [← h]
      exact ringChar.Nat.cast_ringChar
    apply Ring.two_ne_zero hK2
    have := congrArg (fixSubfield σ).subtype h0
    rw [map_natCast, map_zero] at this
    exact_mod_cast this
  have : IsSimpleGroup (adjointGroup τ (fixSubfield σ)) :=
    (odd_pinned_Chevalley_p_components τ (fixSubfield σ) hk2).1
  let eJ : fixedFieldImage τ σ ≃* adjointGroup τ (fixSubfield σ) :=
    ((adjointGroup τ (fixSubfield σ)).equivMapOfInjective _ (baseChangeGL_injective _)).symm
  let eJC : (fixedFieldImage τ σ).subgroupOf (adjointGroup τ K) ≃* fixedFieldImage τ σ :=
    Subgroup.subgroupOfEquivOfLe hJC
  have hJs : IsSimpleGroup ((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)) :=
    (eJC.trans eJ).isSimpleGroup
  have hJn : ∃ x y : (fixedFieldImage τ σ).subgroupOf (adjointGroup τ K), x * y ≠ y * x := by
    by_contra hcon
    push Not at hcon
    apply not_commute_fixedFieldImage τ.rank_pos σ
    intro a b
    have h := hcon (eJC.symm a) (eJC.symm b)
    apply eJC.symm.injective
    rw [map_mul, map_mul]
    exact h
  have hmemΓ : ∀ g : adjointGroup τ K,
      g ∈ (entrywiseFixedGroup τ σ).subgroupOf (adjointGroup τ K) ↔
        entrywiseAdjointAut τ σ g = g := fun g => by
    rw [Subgroup.mem_subgroupOf, mem_entrywiseFixedGroup]
    constructor
    · rintro ⟨-, h⟩
      exact Subtype.ext ((coe_entrywiseAdjointAut τ σ g).trans h)
    · intro h
      exact ⟨g.2, (coe_entrywiseAdjointAut τ σ g).symm.trans (congrArg Subtype.val h)⟩
  have hJN : (fixedFieldImage τ σ).subgroupOf (adjointGroup τ K) ≤
      (entrywiseFixedGroup τ σ).subgroupOf (adjointGroup τ K) := fun g hg => hJΓ hg
  have hΓnorm : entrywiseFixedGroup τ σ ≤
      Subgroup.normalizer (fixedFieldImage τ σ : Set (ModGL τ K)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJΓ).1 fixedFieldImage_normal
  have hJnorm : (((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)).subgroupOf
      ((entrywiseFixedGroup τ σ).subgroupOf (adjointGroup τ K))).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hJN).2 fun g hg => ?_
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.1 (hΓnorm hg) (h : ModGL τ K)
  have hJst : ∀ β : MulAut (adjointGroup τ K),
      (∀ x ∈ (fixedFieldImage τ σ).subgroupOf (adjointGroup τ K), β x = x) →
        β ∈ Subgroup.zpowers (entrywiseAdjointAut τ σ) := by
    intro β hβ
    obtain ⟨η, hηk, hβη⟩ := hfixer β fun j hj => hβ j (Subgroup.mem_subgroupOf.2 hj)
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 (mem_zpowers_of_fixed hηk)
    refine Subgroup.mem_zpowers_iff.2 ⟨n, ?_⟩
    rw [hβη]
    exact (map_zpow (entrywiseAdjointAutHom (τ := τ)) σ n).symm
  exact fixedClauses_of_simple_normal_stabilizer hp hsC hnC hpC
    (by rw [orderOf_entrywiseAdjointAut τ.rank_pos σ, hσ]) hJN hJnorm hJs hJn
    (fun t => (hmemΓ t).symm) hJst hNL

theorem fieldClauses_odd_of_normalForm
    {τ : Tag} {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f) (hp : p.Prime)
    (hpC : ¬ p ∣ Nat.card (adjointGroup τ K))
    (hNF : ∀ η : MulAut (adjointGroup τ K), ∃! gβ : adjointGroup τ K × (K ≃+* K),
      η = MulAut.conj gβ.1 * entrywiseAdjointAut τ gβ.2)
    (hNL : ChevalleySubfieldNL τ K p) : FieldClauses p (adjointGroup τ K) := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hK
  have : Fact p.Prime := ⟨hp⟩
  rintro ⟨α, hα⟩
  obtain ⟨⟨x, σ⟩, hxσ, -⟩ := hNF α
  simp only at hxσ
  have hσp : orderOf σ = p := by
    have hpow : α ^ p = 1 := by
      rw [← hα]
      exact pow_orderOf_eq_one _
    rw [hxσ, conj_mul_pow, ← entrywiseAdjointAut_pow] at hpow
    have h1 : MulAut.conj (((List.range p).map fun i => (entrywiseAdjointAut τ σ ^ i) x).prod) *
        entrywiseAdjointAut τ (σ ^ p) = MulAut.conj 1 * entrywiseAdjointAut τ 1 := by
      rw [hpow, map_one, entrywiseAdjointAut_one, one_mul]
    have hσ1 : σ ≠ 1 := by
      intro h
      apply hpC
      have hαx : α = MulAut.conj x := by rw [hxσ, h, entrywiseAdjointAut_one, mul_one]
      have hd : orderOf α ∣ Nat.card (adjointGroup τ K) := by
        rw [hαx]
        exact (orderOf_map_dvd (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K))
          x).trans (orderOf_dvd_natCard x)
      rwa [hα] at hd
    exact orderOf_eq_prime (eq_of_conj_mul_entrywiseAdjointAut_eq hNF h1).2 hσ1
  have hf₀ : orderOf (entrywiseAdjointAut τ σ) = p := by
    rw [orderOf_entrywiseAdjointAut τ.rank_pos σ, hσp]
  exact ⟨entrywiseAdjointAut τ σ, hf₀, fixedClauses_odd_of_fixer hℓ2 hp hpC σ hσp
    (odd_hfixer_of_normalForm hℓ2 (fun η => (hNF η).exists) σ)
    fun _ => nonLocalized_fixed_entrywiseAdjointAut σ (hNL σ hσp)⟩

theorem fieldClauses_oddF4
    {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (K : Type)
    [Field K] (hK : Nat.card K = ℓ ^ f) (hp : p.Prime)
    (hpC : ¬ p ∣ Nat.card (adjointGroup .F4 K))
    (hNL : ChevalleySubfieldNL .F4 K p) : FieldClauses p (adjointGroup .F4 K) :=
  fieldClauses_odd_of_normalForm hℓ hℓ2 hf K hK hp hpC
    (conj_normalForm_of_pointwise
      (odd_F4_and_nonexceptional_G2_automorphism_normal_form hℓ hℓ2 hf K hK .F4 (Or.inl rfl)).1)
    hNL

theorem fieldClauses_oddG2
    {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f) (hp : p.Prime)
    (hpC : ¬ p ∣ Nat.card (adjointGroup .G2 K))
    (hNL : ChevalleySubfieldNL .G2 K p) : FieldClauses p (adjointGroup .G2 K) :=
  fieldClauses_odd_of_normalForm hℓ hℓ2 hf K hK hp hpC
    (conj_normalForm_of_pointwise
      (odd_F4_and_nonexceptional_G2_automorphism_normal_form hℓ hℓ2 hf K hK .G2
        (Or.inr ⟨rfl, hℓ3⟩)).1)
    hNL

theorem fieldClauses_oddE8
    {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (K : Type)
    [Field K] (hK : Nat.card K = ℓ ^ f) (hp : p.Prime)
    (hpC : ¬ p ∣ Nat.card (adjointGroup .E8 K))
    (hNL : ChevalleySubfieldNL .E8 K p) : FieldClauses p (adjointGroup .E8 K) :=
  fieldClauses_odd_of_normalForm hℓ hℓ2 hf K hK hp hpC
    (odd_E8_inner_field_automorphisms_and_noninner_prime_core hℓ hℓ2 hf K hK).1 hNL

theorem untwistedChevalleyModel_adjointGroup
    {τ : Tag} {K : Type} [Field K] [Finite K] {q : ℕ}
    (hK : Nat.card K = q) : UntwistedChevalleyModel (adjointGroup τ K) τ q :=
  ⟨K, inferInstance, inferInstance, hK, ⟨((QuotientGroup.quotientMulEquivOfEq
    center_adjointGroup_eq_bot).trans QuotientGroup.quotientBot).symm⟩⟩

theorem fieldClauses_chevalleyOddF4
    {T : Type} [Group T] [Finite T] (hs : IsSimpleGroup T)
    {ℓ f p : ℕ} (hm : CFSG.Blueprint.ChevalleyExceptionalModel T .F4 ℓ f) (hℓ2 : ℓ ≠ 2)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpT : ¬ p ∣ Nat.card T)
    (hNL : SubfieldNonLocalizedChevalley) : FieldClauses p T := by
  obtain ⟨hadm, hmod⟩ := hm
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_adjointGroup_of_untwisted hmod
  have : IsSimpleGroup T := hs
  have : Finite (adjointGroup .F4 K) := Finite.of_equiv T e.symm.toEquiv
  have hsC : IsSimpleGroup (adjointGroup .F4 K) := e.isSimpleGroup
  have hpC : ¬ p ∣ Nat.card (adjointGroup .F4 K) := by rwa [Nat.card_congr e.toEquiv]
  exact FieldClauses.of_mulEquiv e
    (fieldClauses_oddF4 hadm.1 hℓ2 hadm.2.1 K hK hp hpC
      (ChevalleySubfieldNL.of_chevalley hNL (Or.inr (Or.inl rfl)) hsC hp hp2 hpC))

theorem fieldClauses_chevalleyOddG2
    {T : Type} [Group T] [Finite T] (hs : IsSimpleGroup T)
    {ℓ f p : ℕ} (hm : CFSG.Blueprint.ChevalleyExceptionalModel T .G2 ℓ f) (hℓ2 : ℓ ≠ 2)
    (hℓ3 : ℓ ≠ 3) (hp : p.Prime) (hp2 : p ≠ 2) (hpT : ¬ p ∣ Nat.card T)
    (hNL : SubfieldNonLocalizedChevalley) : FieldClauses p T := by
  obtain ⟨hadm, hmod⟩ := hm
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_adjointGroup_of_untwisted hmod
  have : IsSimpleGroup T := hs
  have : Finite (adjointGroup .G2 K) := Finite.of_equiv T e.symm.toEquiv
  have hsC : IsSimpleGroup (adjointGroup .G2 K) := e.isSimpleGroup
  have hpC : ¬ p ∣ Nat.card (adjointGroup .G2 K) := by rwa [Nat.card_congr e.toEquiv]
  exact FieldClauses.of_mulEquiv e
    (fieldClauses_oddG2 hadm.1 hℓ2 hℓ3 hadm.2.1 K hK hp hpC
      (ChevalleySubfieldNL.of_chevalley hNL (Or.inl rfl) hsC hp hp2 hpC))

theorem fieldClauses_chevalleyOddE8
    {T : Type} [Group T] [Finite T] (hs : IsSimpleGroup T)
    {ℓ f p : ℕ} (hm : CFSG.Blueprint.ChevalleyExceptionalModel T .E8 ℓ f) (hℓ2 : ℓ ≠ 2)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpT : ¬ p ∣ Nat.card T)
    (hNL : SubfieldNonLocalizedChevalley) : FieldClauses p T := by
  obtain ⟨hadm, hmod⟩ := hm
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_adjointGroup_of_untwisted hmod
  have : IsSimpleGroup T := hs
  have : Finite (adjointGroup .E8 K) := Finite.of_equiv T e.symm.toEquiv
  have hsC : IsSimpleGroup (adjointGroup .E8 K) := e.isSimpleGroup
  have hpC : ¬ p ∣ Nat.card (adjointGroup .E8 K) := by rwa [Nat.card_congr e.toEquiv]
  exact FieldClauses.of_mulEquiv e
    (fieldClauses_oddE8 hadm.1 hℓ2 hadm.2.1 K hK hp hpC
      (ChevalleySubfieldNL.of_chevalley hNL (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hsC hp hp2
        hpC))

end CFSG.SignalizerFunctorTheorem.CatalogBridge
