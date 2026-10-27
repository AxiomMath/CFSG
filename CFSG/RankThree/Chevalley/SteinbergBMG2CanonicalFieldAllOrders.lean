module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.RankThree.Chevalley.SteinbergBTCanonicalFieldCommon

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog (ringAut_commute mem_zpowers_of_fixed
  entrywiseFixedGroup_eq_fixedFieldImage entrywise_baseChangeGL_restrict
  ringEquiv_eq_refl_of_card_two units_map_entrywise_refl_k
  even_G2_exact_automorphism_normal_form)

variable {K : Type} [Field K]

theorem eq_one_of_forall_fixedFieldImage_of_card [Finite K] {d : ℕ} (hd : 1 ≤ d)
    {σ : K ≃+* K} (hk : Nat.card (fixSubfield σ) = 2 ^ d) {g : adjointGroup .G2 K}
    (hgJ : (g : ModGL .G2 K) ∈ fixedFieldImage .G2 σ) (η : K ≃+* K)
    (hfix : ∀ j : adjointGroup .G2 K, (j : ModGL .G2 K) ∈ fixedFieldImage .G2 σ →
      (g : ModGL .G2 K) * Units.map (entrywiseHom η.toRingHom) (j : ModGL .G2 K) *
        (g : ModGL .G2 K)⁻¹ = j) :
    g = 1 ∧ ∀ c ∈ fixSubfield σ, η c = c := by
  set k := fixSubfield σ
  have : Finite k := Subtype.finite
  set ι := baseChangeGL (τ := .G2) k.subtype
  have hιinj : Function.Injective ι := baseChangeGL_injective _
  obtain ⟨g', hg', hgg'⟩ := hgJ
  set ψ := fixSubfieldRestrict η σ
  have hid : ∀ j' ∈ adjointGroup .G2 k,
      g' * Units.map (entrywiseHom ψ.toRingHom) j' * g'⁻¹ = j' := by
    intro j' hj'
    have hj'J : ι j' ∈ fixedFieldImage .G2 σ := ⟨j', hj', rfl⟩
    have hj'C : ι j' ∈ adjointGroup .G2 K := (fixedFieldImage_le hj'J).1
    have h1 := hfix ⟨ι j', hj'C⟩ hj'J
    change (g : ModGL .G2 K) * Units.map (entrywiseHom η.toRingHom) (ι j') *
      (g : ModGL .G2 K)⁻¹ = ι j' at h1
    rw [← hgg', entrywise_baseChangeGL_restrict, ← map_inv, ← map_mul, ← map_mul] at h1
    exact hιinj h1
  have hψ : ψ = RingEquiv.refl k ∧ g' = 1 := by
    rcases Nat.lt_or_ge 1 d with hd2 | hd1
    ·
      obtain ⟨hNF, -⟩ := even_G2_exact_automorphism_normal_form hd2 k hk
      obtain ⟨q, -, hq⟩ := hNF 1
      have h1 := hq (1, RingEquiv.refl k) fun h => by
        simp only [MulAut.one_apply, OneMemClass.coe_one, inv_one, one_mul, mul_one]
        exact (units_map_entrywise_refl_k (h : ModGL .G2 k)).symm
      have h2 := hq (⟨g', hg'⟩, ψ) fun h => (hid h h.2).symm
      have h3 := h2.trans h1.symm
      exact ⟨congrArg Prod.snd h3, congrArg (fun x => (x.1 : ModGL .G2 k)) h3⟩
    ·
      have hd1' : d = 1 := le_antisymm hd1 hd
      have hk2 : Nat.card k = 2 := by rw [hk, hd1', pow_one]
      have hψ1 := ringEquiv_eq_refl_of_card_two hk2 ψ
      refine ⟨hψ1, ?_⟩
      have hZ : Subgroup.center (adjointGroup .G2 k) = ⊥ := center_adjointGroup_eq_bot
      have hc : (⟨g', hg'⟩ : adjointGroup .G2 k) ∈ Subgroup.center (adjointGroup .G2 k) := by
        refine Subgroup.mem_center_iff.2 fun j => Subtype.ext ?_
        have h1 := hid j j.2
        rw [hψ1, units_map_entrywise_refl_k] at h1
        change (j : ModGL .G2 k) * g' = g' * j
        rw [← mul_inv_eq_iff_eq_mul.1 h1]
      rw [hZ, Subgroup.mem_bot] at hc
      exact congrArg Subtype.val hc
  obtain ⟨hψ1, hg'1⟩ := hψ
  refine ⟨Subtype.ext ?_, fun c hc => ?_⟩
  · rw [← hgg', hg'1, map_one]
    rfl
  · have h1 := congrArg (fun ψ' : k ≃+* k => (ψ' ⟨c, hc⟩ : K)) hψ1
    simp only [ψ] at h1
    exact h1

theorem even_G2_canonical_field_centralizer_all_orders {f : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card K = 2 ^ f) (σ : K ≃+* K) :
    orderOf σ ∣ f ∧ Nat.card (fixSubfield σ) = 2 ^ (f / orderOf σ) ∧
      fixedFieldImage .G2 σ ≤ adjointGroup .G2 K ∧
      ((entrywiseAdjointAut .G2 σ).toMonoidHom.eqLocus (MonoidHom.id _)).map
          (adjointGroup .G2 K).subtype = fixedFieldImage .G2 σ ∧
      (∃ ι : ↥((fixedFieldImage .G2 σ).subgroupOf (adjointGroup .G2 K)) ≃*
          ↥(((fixedFieldImage .G2 σ).subgroupOf (adjointGroup .G2 K)).map MulAut.conj),
        ∀ j, (ι j : MulAut (adjointGroup .G2 K)) = MulAut.conj (j : adjointGroup .G2 K)) ∧
      (∀ β ∈ Subgroup.centralizer {entrywiseAdjointAut .G2 σ},
        ∃! gη : adjointGroup .G2 K × (K ≃+* K), (gη.1 : ModGL .G2 K) ∈ fixedFieldImage .G2 σ ∧
          ∀ h : adjointGroup .G2 K, (β h : ModGL .G2 K) = (gη.1 : ModGL .G2 K) *
            Units.map (entrywiseHom gη.2.toRingHom) (h : ModGL .G2 K) *
              (gη.1 : ModGL .G2 K)⁻¹) ∧
      (∀ g : adjointGroup .G2 K, (g : ModGL .G2 K) ∈ fixedFieldImage .G2 σ → ∀ η : K ≃+* K,
        MulAut.conj g * entrywiseAdjointAut .G2 η ∈
          Subgroup.centralizer {entrywiseAdjointAut .G2 σ}) ∧
      ((fixedFieldImage .G2 σ).subgroupOf (adjointGroup .G2 K)).map MulAut.conj ≤
        Subgroup.centralizer {entrywiseAdjointAut .G2 σ} ∧
      ((((fixedFieldImage .G2 σ).subgroupOf (adjointGroup .G2 K)).map MulAut.conj).subgroupOf
        (Subgroup.centralizer {entrywiseAdjointAut .G2 σ})).Normal ∧
      ((Subgroup.centralizer {entrywiseAdjointAut .G2 σ} ⊓
          Subgroup.centralizer ((((fixedFieldImage .G2 σ).subgroupOf
            (adjointGroup .G2 K)).map MulAut.conj : Subgroup (MulAut (adjointGroup .G2 K))) :
              Set (MulAut (adjointGroup .G2 K))) : Subgroup (MulAut (adjointGroup .G2 K))) :
          Set (MulAut (adjointGroup .G2 K))) =
        {β | ∃ η : K ≃+* K, (∀ c ∈ fixSubfield σ, η c = c) ∧ β = entrywiseAdjointAut .G2 η} ∧
      Subgroup.centralizer {entrywiseAdjointAut .G2 σ} ⊓
          Subgroup.centralizer ((((fixedFieldImage .G2 σ).subgroupOf
            (adjointGroup .G2 K)).map MulAut.conj : Subgroup (MulAut (adjointGroup .G2 K))) :
              Set (MulAut (adjointGroup .G2 K))) =
        Subgroup.zpowers (entrywiseAdjointAut .G2 σ) ∧
      IsCyclic (Subgroup.zpowers (entrywiseAdjointAut .G2 σ)) ∧
      Nat.card (Subgroup.zpowers (entrywiseAdjointAut .G2 σ)) = orderOf σ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hZ : Subgroup.center (adjointGroup .G2 K) = ⊥ := center_adjointGroup_eq_bot
  have hinj := mulAut_conj_injective_of_center_eq_bot hZ
  have hrank : 0 < Tag.G2.rank := by decide
  obtain ⟨hdvd, hk⟩ := SteinbergBT.card_fixSubfield Nat.prime_two (by omega) hK σ
  have hd : 1 ≤ f / orderOf σ :=
    Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) (Nat.pos_of_dvd_of_pos hdvd (by omega))
  set δ := entrywiseAdjointAut .G2 σ with hδ
  set J := fixedFieldImage .G2 σ with hJ
  have hΓJ := entrywiseFixedGroup_eq_fixedFieldImage σ
  have hJC : J ≤ adjointGroup .G2 K := fun j hj => (fixedFieldImage_le hj).1
  have hmemJ : ∀ g : adjointGroup .G2 K, (g : ModGL .G2 K) ∈ J ↔ δ g = g := by
    intro g
    rw [hJ, ← hΓJ, mem_entrywiseFixedGroup]
    constructor
    · rintro ⟨-, h⟩
      exact Subtype.ext h
    · intro h
      exact ⟨g.2, congrArg Subtype.val h⟩
  obtain ⟨hNF, -⟩ := even_G2_exact_automorphism_normal_form hf K hK
  have hcommδ : ∀ η : K ≃+* K, entrywiseAdjointAut .G2 η * δ = δ * entrywiseAdjointAut .G2 η :=
    fun η => by rw [hδ, ← entrywiseAdjointAut_mul, ← entrywiseAdjointAut_mul, ringAut_commute]
  have hform : ∀ (β : MulAut (adjointGroup .G2 K)) (g : adjointGroup .G2 K) (η : K ≃+* K),
      (∀ h : adjointGroup .G2 K, (β h : ModGL .G2 K) = (g : ModGL .G2 K) *
        Units.map (entrywiseHom η.toRingHom) (h : ModGL .G2 K) * (g : ModGL .G2 K)⁻¹) →
      β = MulAut.conj g * entrywiseAdjointAut .G2 η := fun β g η h =>
    MulEquiv.ext fun x => Subtype.ext (by
      rw [h x, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        coe_entrywiseAdjointAut, Subgroup.coe_inv])
  have hconjδ : ∀ (g : adjointGroup .G2 K) (η : K ≃+* K),
      δ * (MulAut.conj g * entrywiseAdjointAut .G2 η) =
        MulAut.conj (δ g) * (δ * entrywiseAdjointAut .G2 η) := fun g η => by
    rw [← mul_assoc, mulAut_mul_conj, mul_assoc]
  have hcentJ : ∀ β ∈ Subgroup.centralizer {δ}, ∀ (g : adjointGroup .G2 K) (η : K ≃+* K),
      (∀ h : adjointGroup .G2 K, (β h : ModGL .G2 K) = (g : ModGL .G2 K) *
        Units.map (entrywiseHom η.toRingHom) (h : ModGL .G2 K) * (g : ModGL .G2 K)⁻¹) →
      (g : ModGL .G2 K) ∈ J := by
    intro β hβ g η h
    have hβδ : δ * β = β * δ := Subgroup.mem_centralizer_iff.1 hβ δ (Set.mem_singleton δ)
    rw [hform β g η h] at hβδ
    have e1 : MulAut.conj (δ g) * (δ * entrywiseAdjointAut .G2 η) =
        MulAut.conj g * (δ * entrywiseAdjointAut .G2 η) := by
      rw [← hconjδ, hβδ, mul_assoc, hcommδ]
    exact (hmemJ g).2 (hinj (mul_right_cancel e1))
  have hactor : ∀ g : adjointGroup .G2 K, (g : ModGL .G2 K) ∈ J → ∀ η : K ≃+* K,
      MulAut.conj g * entrywiseAdjointAut .G2 η ∈ Subgroup.centralizer {δ} := by
    intro g hg η
    refine Subgroup.mem_centralizer_iff.2 fun x hx => ?_
    rw [Set.mem_singleton_iff.1 hx, hconjδ, (hmemJ g).1 hg, mul_assoc, ← hcommδ, ← mul_assoc]
  have hNδ : ((J.subgroupOf (adjointGroup .G2 K)).map MulAut.conj) ≤
      Subgroup.centralizer {δ} := by
    rintro _ ⟨j, hj, rfl⟩
    refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    rw [Set.mem_singleton_iff.1 hh, mulAut_mul_conj,
      (hmemJ j).1 (Subgroup.mem_subgroupOf.1 hj)]
  have hpoint : ∀ β ∈ Subgroup.centralizer {δ} ⊓ Subgroup.centralizer
      (((J.subgroupOf (adjointGroup .G2 K)).map MulAut.conj : Subgroup _) :
        Set (MulAut (adjointGroup .G2 K))),
      ∃ η : K ≃+* K, (∀ c ∈ fixSubfield σ, η c = c) ∧ β = entrywiseAdjointAut .G2 η := by
    intro β hβ
    obtain ⟨hβδ, hβN⟩ := Subgroup.mem_inf.1 hβ
    obtain ⟨⟨g, η⟩, hgη, -⟩ := hNF β
    have hgJ := hcentJ β hβδ g η hgη
    have hfix : ∀ j : adjointGroup .G2 K, (j : ModGL .G2 K) ∈ J →
        (g : ModGL .G2 K) * Units.map (entrywiseHom η.toRingHom) (j : ModGL .G2 K) *
          (g : ModGL .G2 K)⁻¹ = j := by
      intro j hj
      have hn : MulAut.conj j ∈ (J.subgroupOf (adjointGroup .G2 K)).map MulAut.conj :=
        ⟨j, Subgroup.mem_subgroupOf.2 hj, rfl⟩
      have h1 : MulAut.conj j * β = β * MulAut.conj j :=
        Subgroup.mem_centralizer_iff.1 hβN _ hn
      have h2 : MulAut.conj (β j) = MulAut.conj j := by
        rw [← mulAut_mul_conj_mul_inv, ← h1, mul_inv_cancel_right]
      rw [← hgη j, hinj h2]
    obtain ⟨hg1, hηk⟩ := eq_one_of_forall_fixedFieldImage_of_card hd hk hgJ η hfix
    refine ⟨η, hηk, ?_⟩
    rw [hform β g η hgη, hg1, map_one, one_mul]
  have hzp : ∀ η : K ≃+* K, (∀ c ∈ fixSubfield σ, η c = c) →
      entrywiseAdjointAut .G2 η ∈ Subgroup.zpowers δ := by
    intro η hη
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 (mem_zpowers_of_fixed fun x hx => hη x hx)
    exact Subgroup.mem_zpowers_iff.2
      ⟨n, (map_zpow (entrywiseAdjointAutHom (τ := .G2)) σ n).symm⟩
  have hδle : Subgroup.zpowers δ ≤ Subgroup.centralizer {δ} ⊓ Subgroup.centralizer
      (((J.subgroupOf (adjointGroup .G2 K)).map MulAut.conj : Subgroup _) :
        Set (MulAut (adjointGroup .G2 K))) :=
    Subgroup.zpowers_le.2 (Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2
      fun h hh => by rw [Set.mem_singleton_iff.1 hh], Subgroup.mem_centralizer_iff.2
        fun n hn => (Subgroup.mem_centralizer_iff.1 (hNδ hn) δ (Set.mem_singleton δ)).symm⟩)
  have hCMN : Subgroup.centralizer {δ} ⊓ Subgroup.centralizer
      (((J.subgroupOf (adjointGroup .G2 K)).map MulAut.conj : Subgroup _) :
        Set (MulAut (adjointGroup .G2 K))) = Subgroup.zpowers δ := by
    refine le_antisymm (fun β hβ => ?_) hδle
    obtain ⟨η, hη, rfl⟩ := hpoint β hβ
    exact hzp η hη
  refine ⟨hdvd, hk, hJC, ?_,
    ⟨(J.subgroupOf (adjointGroup .G2 K)).equivMapOfInjective _ hinj, fun j => rfl⟩,
    fun β hβ => ?_, hactor, hNδ, ⟨fun n hn g => ?_⟩, ?_, hCMN, inferInstance, by
      rw [Nat.card_zpowers, SteinbergBT.orderOf_entrywiseAdjointAut hrank σ]⟩
  ·
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact (hmemJ g).2 hg
    · intro hx
      exact ⟨⟨x, hJC hx⟩, (hmemJ _).1 hx, rfl⟩
  ·
    obtain ⟨⟨g, η⟩, hgη, huniq⟩ := hNF β
    exact ⟨(g, η), ⟨hcentJ β hβ g η hgη, hgη⟩, fun q hq => huniq q hq.2⟩
  ·
    obtain ⟨j, hj, hjn⟩ := Subgroup.mem_subgroupOf.1 hn
    rw [SetLike.mem_coe] at hj
    have hgδ : δ * (g : MulAut (adjointGroup .G2 K)) = g * δ :=
      Subgroup.mem_centralizer_iff.1 g.2 δ (Set.mem_singleton δ)
    refine Subgroup.mem_subgroupOf.2 ⟨(g : MulAut (adjointGroup .G2 K)) j, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, hmemJ]
      calc δ ((g : MulAut (adjointGroup .G2 K)) j) =
          (δ * (g : MulAut (adjointGroup .G2 K))) j := rfl
        _ = (g * δ : MulAut (adjointGroup .G2 K)) j := by rw [hgδ]
        _ = (g : MulAut (adjointGroup .G2 K)) (δ j) := rfl
        _ = (g : MulAut (adjointGroup .G2 K)) j := by
            rw [(hmemJ j).1 (Subgroup.mem_subgroupOf.1 hj)]
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hjn]
      exact (mulAut_mul_conj_mul_inv _ _).symm
  ·
    ext β
    constructor
    · exact hpoint β
    · rintro ⟨η, hη, rfl⟩
      exact hδle (hzp η hη)

end CFSG.RankThree.Chevalley
