module

public import CFSG.LieType.Chevalley.EvenCanonicalFieldCentralizer
public import CFSG.LieType.Chevalley.E6FieldGraphFieldPointwiseCentralizer

public noncomputable section

namespace CFSG.RankThree.Chevalley.SteinbergBT

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog (ringAut_commute mem_zpowers_of_fixed)

variable {τ : Tag} {K : Type} [Field K]

theorem card_fixSubfield {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f)
    (σ : K ≃+* K) : orderOf σ ∣ f ∧ Nat.card (fixSubfield σ) = p ^ (f / orderOf σ) := by
  obtain ⟨-, -, -, -, -, hA⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hp hf hK
  obtain ⟨hdvd, S, hS, hcard⟩ := hA (Subgroup.zpowers σ)
  rw [Nat.card_zpowers] at hdvd hcard
  refine ⟨hdvd, ?_⟩
  have hSk : S = fixSubfield σ := by
    refine SetLike.ext' ?_
    rw [hS]
    ext a
    simp only [Set.mem_ofPred_eq, SetLike.mem_coe, mem_fixSubfield]
    constructor
    · intro h
      exact h σ (Subgroup.mem_zpowers σ)
    · intro h τ' hτ'
      have hstab : Subgroup.zpowers σ ≤ MulAction.stabilizer (K ≃+* K) a :=
        Subgroup.zpowers_le.2 (by rw [MulAction.mem_stabilizer_iff, RingAut.smul_def]; exact h)
      have h' := hstab hτ'
      rwa [MulAction.mem_stabilizer_iff, RingAut.smul_def] at h'
  rw [← hSk, hcard]

theorem pow_card_eq_self_of_mem {k : Subfield K} [Finite k] {p d : ℕ}
    (hk : Nat.card k = p ^ d) {c : K} (hc : c ∈ k) : c ^ p ^ d = c := by
  have : Fintype k := Fintype.ofFinite k
  have h := FiniteField.pow_card (⟨c, hc⟩ : k)
  rw [← Nat.card_eq_fintype_card, hk] at h
  exact congrArg Subtype.val h

theorem entrywiseAdjointAutHom_injective (hr : 0 < τ.rank) :
    Function.Injective (entrywiseAdjointAutHom (τ := τ) (K := K)) := by
  rw [injective_iff_map_eq_one]
  intro φ h
  refine RingEquiv.ext fun c => ?_
  have h1 := congrArg (fun β : MulAut (adjointGroup τ K) => β (adjX τ K ⟨0, hr⟩ c)) h
  change entrywiseAdjointAut τ φ (adjX τ K ⟨0, hr⟩ c) = adjX τ K ⟨0, hr⟩ c at h1
  rw [FieldGraphFieldPointwise.entrywiseAdjointAut_adjX] at h1
  exact adjX_injective _ h1

theorem entrywiseAdjointAut_xElement (φ : K ≃+* K) (i : Fin τ.rank) (c : K) :
    entrywiseAdjointAut τ φ (xElement i c) = xElement i (φ c) :=
  Subtype.ext (units_map_entrywiseHom_xUnit φ.toRingHom i c)

theorem entrywiseAdjointAut_yElement (φ : K ≃+* K) (i : Fin τ.rank) (c : K) :
    entrywiseAdjointAut τ φ (yElement i c) = yElement i (φ c) :=
  Subtype.ext (units_map_entrywiseHom_yUnit φ.toRingHom i c)

theorem orderOf_entrywiseAdjointAut (hr : 0 < τ.rank) (σ : K ≃+* K) :
    orderOf (entrywiseAdjointAut τ σ) = orderOf σ :=
  orderOf_injective _ (entrywiseAdjointAutHom_injective hr) σ

theorem not_commute_fixedFieldImage (hr : 0 < τ.rank) (σ : K ≃+* K) :
    ¬∀ a b : fixedFieldImage τ σ, a * b = b * a := by
  intro h
  set i : Fin τ.rank := ⟨0, hr⟩
  have hx : xUnit τ K i 1 ∈ fixedFieldImage τ σ := xUnit_mem_fixedFieldImage i (map_one σ)
  have hy : yUnit τ K i 1 ∈ fixedFieldImage τ σ := yUnit_mem_fixedFieldImage i (map_one σ)
  exact not_commute_xUnit_yUnit (τ := τ) (K := K) i
    (congrArg Subtype.val (h ⟨_, hx⟩ ⟨_, hy⟩))

theorem canonical_field_centralizer_of_normalForm_all [Finite K] (σ : K ≃+* K)
    (hNF : ∀ α : MulAut (adjointGroup τ K), ∃! gφ : adjointGroup τ K × (K ≃+* K),
      ∀ h : adjointGroup τ K, (α h : ModGL τ K) = (gφ.1 : ModGL τ K) *
        Units.map (entrywiseHom gφ.2.toRingHom) (h : ModGL τ K) * (gφ.1 : ModGL τ K)⁻¹)
    (hNFk : ∀ α : MulAut (adjointGroup τ (fixSubfield σ)),
      ∃! gψ : adjointGroup τ (fixSubfield σ) × (fixSubfield σ ≃+* fixSubfield σ),
        ∀ h : adjointGroup τ (fixSubfield σ), (α h : ModGL τ (fixSubfield σ)) =
          (gψ.1 : ModGL τ (fixSubfield σ)) *
            Units.map (entrywiseHom gψ.2.toRingHom) (h : ModGL τ (fixSubfield σ)) *
              (gψ.1 : ModGL τ (fixSubfield σ))⁻¹)
    (hΓJ : entrywiseFixedGroup τ σ = fixedFieldImage τ σ) :
    fixedFieldImage τ σ ≤ adjointGroup τ K ∧
      ((entrywiseAdjointAut τ σ).toMonoidHom.eqLocus (MonoidHom.id _)).map
          (adjointGroup τ K).subtype = fixedFieldImage τ σ ∧
      (∃ ι : ↥((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)) ≃*
          ↥(((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)).map MulAut.conj),
        ∀ j, (ι j : MulAut (adjointGroup τ K)) = MulAut.conj (j : adjointGroup τ K)) ∧
      (∀ β ∈ Subgroup.centralizer {entrywiseAdjointAut τ σ},
        ∃! gφ : adjointGroup τ K × (K ≃+* K), (gφ.1 : ModGL τ K) ∈ fixedFieldImage τ σ ∧
          ∀ h : adjointGroup τ K, (β h : ModGL τ K) = (gφ.1 : ModGL τ K) *
            Units.map (entrywiseHom gφ.2.toRingHom) (h : ModGL τ K) *
              (gφ.1 : ModGL τ K)⁻¹) ∧
      (∀ g : adjointGroup τ K, (g : ModGL τ K) ∈ fixedFieldImage τ σ → ∀ φ : K ≃+* K,
        MulAut.conj g * entrywiseAdjointAut τ φ ∈
          Subgroup.centralizer {entrywiseAdjointAut τ σ}) ∧
      ((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)).map MulAut.conj ≤
        Subgroup.centralizer {entrywiseAdjointAut τ σ} ∧
      ((((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)).map MulAut.conj).subgroupOf
        (Subgroup.centralizer {entrywiseAdjointAut τ σ})).Normal ∧
      Subgroup.centralizer {entrywiseAdjointAut τ σ} ⊓
          Subgroup.centralizer ((((fixedFieldImage τ σ).subgroupOf
            (adjointGroup τ K)).map MulAut.conj : Subgroup (MulAut (adjointGroup τ K))) :
              Set (MulAut (adjointGroup τ K))) =
        Subgroup.zpowers (entrywiseAdjointAut τ σ) := by
  have hZ : Subgroup.center (adjointGroup τ K) = ⊥ := center_adjointGroup_eq_bot
  have hinj := mulAut_conj_injective_of_center_eq_bot hZ
  set δ := entrywiseAdjointAut τ σ with hδ
  set J := fixedFieldImage τ σ with hJ
  have hJC : J ≤ adjointGroup τ K := fun j hj => (fixedFieldImage_le hj).1
  have hmemJ : ∀ g : adjointGroup τ K, (g : ModGL τ K) ∈ J ↔ δ g = g := by
    intro g
    refine (Subgroup.ext_iff.1 hΓJ (g : ModGL τ K)).symm.trans ?_
    rw [mem_entrywiseFixedGroup]
    constructor
    · rintro ⟨-, h⟩
      exact Subtype.ext h
    · intro h
      exact ⟨g.2, congrArg Subtype.val h⟩
  have hcommδ : ∀ φ : K ≃+* K, entrywiseAdjointAut τ φ * δ = δ * entrywiseAdjointAut τ φ :=
    fun φ => by rw [hδ, ← entrywiseAdjointAut_mul, ← entrywiseAdjointAut_mul, ringAut_commute]
  have hform : ∀ (β : MulAut (adjointGroup τ K)) (g : adjointGroup τ K) (φ : K ≃+* K),
      (∀ h : adjointGroup τ K, (β h : ModGL τ K) = (g : ModGL τ K) *
        Units.map (entrywiseHom φ.toRingHom) (h : ModGL τ K) * (g : ModGL τ K)⁻¹) →
      β = MulAut.conj g * entrywiseAdjointAut τ φ := fun β g φ h =>
    MulEquiv.ext fun x => Subtype.ext (by
      rw [h x, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        coe_entrywiseAdjointAut, Subgroup.coe_inv])
  have hconjδ : ∀ (g : adjointGroup τ K) (φ : K ≃+* K),
      δ * (MulAut.conj g * entrywiseAdjointAut τ φ) =
        MulAut.conj (δ g) * (δ * entrywiseAdjointAut τ φ) := fun g φ => by
    rw [← mul_assoc, mulAut_mul_conj, mul_assoc]
  have hcentJ : ∀ β ∈ Subgroup.centralizer {δ}, ∀ (g : adjointGroup τ K) (φ : K ≃+* K),
      (∀ h : adjointGroup τ K, (β h : ModGL τ K) = (g : ModGL τ K) *
        Units.map (entrywiseHom φ.toRingHom) (h : ModGL τ K) * (g : ModGL τ K)⁻¹) →
      (g : ModGL τ K) ∈ J := by
    intro β hβ g φ h
    have hβδ : δ * β = β * δ := Subgroup.mem_centralizer_iff.1 hβ δ (Set.mem_singleton δ)
    rw [hform β g φ h] at hβδ
    have e1 : MulAut.conj (δ g) * (δ * entrywiseAdjointAut τ φ) =
        MulAut.conj g * (δ * entrywiseAdjointAut τ φ) := by
      rw [← hconjδ, hβδ, mul_assoc, hcommδ]
    exact (hmemJ g).2 (hinj (mul_right_cancel e1))
  have hactor : ∀ g : adjointGroup τ K, (g : ModGL τ K) ∈ J → ∀ φ : K ≃+* K,
      MulAut.conj g * entrywiseAdjointAut τ φ ∈ Subgroup.centralizer {δ} := by
    intro g hg φ
    refine Subgroup.mem_centralizer_iff.2 fun x hx => ?_
    rw [Set.mem_singleton_iff.1 hx, hconjδ, (hmemJ g).1 hg, mul_assoc, ← hcommδ, ← mul_assoc]
  have hNδ : ((J.subgroupOf (adjointGroup τ K)).map MulAut.conj) ≤
      Subgroup.centralizer {δ} := by
    rintro _ ⟨j, hj, rfl⟩
    refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    rw [Set.mem_singleton_iff.1 hh, mulAut_mul_conj,
      (hmemJ j).1 (Subgroup.mem_subgroupOf.1 hj)]
  refine ⟨hJC, ?_,
    ⟨(J.subgroupOf (adjointGroup τ K)).equivMapOfInjective _ hinj, fun j => rfl⟩,
    fun β hβ => ?_, hactor, hNδ, ⟨fun n hn g => ?_⟩, le_antisymm (fun β hβ => ?_) ?_⟩
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
    have hgδ : δ * (g : MulAut (adjointGroup τ K)) = g * δ :=
      Subgroup.mem_centralizer_iff.1 g.2 δ (Set.mem_singleton δ)
    refine Subgroup.mem_subgroupOf.2 ⟨(g : MulAut (adjointGroup τ K)) j, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, hmemJ]
      calc δ ((g : MulAut (adjointGroup τ K)) j) =
          (δ * (g : MulAut (adjointGroup τ K))) j := rfl
        _ = (g * δ : MulAut (adjointGroup τ K)) j := by rw [hgδ]
        _ = (g : MulAut (adjointGroup τ K)) (δ j) := rfl
        _ = (g : MulAut (adjointGroup τ K)) j := by
            rw [(hmemJ j).1 (Subgroup.mem_subgroupOf.1 hj)]
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hjn]
      exact (mulAut_mul_conj_mul_inv _ _).symm
  ·
    obtain ⟨hβδ, hβN⟩ := Subgroup.mem_inf.1 hβ
    obtain ⟨⟨g, φ⟩, hgφ, -⟩ := hNF β
    have hgJ := hcentJ β hβδ g φ hgφ
    have hfix : ∀ j : adjointGroup τ K, (j : ModGL τ K) ∈ J →
        (g : ModGL τ K) * Units.map (entrywiseHom φ.toRingHom) (j : ModGL τ K) *
          (g : ModGL τ K)⁻¹ = j := by
      intro j hj
      have hn : MulAut.conj j ∈ (J.subgroupOf (adjointGroup τ K)).map MulAut.conj :=
        ⟨j, Subgroup.mem_subgroupOf.2 hj, rfl⟩
      have h1 : MulAut.conj j * β = β * MulAut.conj j :=
        Subgroup.mem_centralizer_iff.1 hβN _ hn
      have h2 : MulAut.conj (β j) = MulAut.conj j := by
        rw [← mulAut_mul_conj_mul_inv, ← h1, mul_inv_cancel_right]
      rw [← hgφ j, hinj h2]
    obtain ⟨hg1, hφk⟩ := eq_one_of_forall_fixedFieldImage_of_normalForm hNFk hgJ φ hfix
    have hφ : φ ∈ Subgroup.zpowers σ := mem_zpowers_of_fixed fun x hx => hφk x hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hφ
    refine Subgroup.mem_zpowers_iff.2 ⟨n, ?_⟩
    rw [hform β g (σ ^ n) hgφ, hg1, map_one, one_mul, hδ]
    exact (map_zpow (entrywiseAdjointAutHom (τ := τ)) σ n).symm
  ·
    refine Subgroup.zpowers_le.2 (Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2
      fun h hh => by rw [Set.mem_singleton_iff.1 hh], Subgroup.mem_centralizer_iff.2
        fun n hn => (Subgroup.mem_centralizer_iff.1 (hNδ hn) δ (Set.mem_singleton δ)).symm⟩)

end CFSG.RankThree.Chevalley.SteinbergBT
