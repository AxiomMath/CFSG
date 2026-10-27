module

public import CFSG.LocalAnalysis.LargeEvenClassification.CoprimeCommutators
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalModelOuterTwoPart

public section

namespace CFSG.RankThree.Classical.SteinbergBY

open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification (OuterAutomorphisms.inner OuterAutomorphisms.inner_normal)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointKernel (similarityPointAction_eq_one_iff)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.LocalAnalysis.ComponentInitial (finite_field_automorphism_fixed_field_cardinality)
open Matrix
open scoped Pointwise commutatorElement

section General

variable {K : Type} [Field K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))

@[expose] noncomputable def familyOrbitKernel : Subgroup (MulAut (matrixProjectiveDerived Q)) :=
  ⨅ Y ∈ MulAction.orbit (MulAut (matrixProjectiveDerived Q)) (projectivePointFamily Q),
    MulAction.stabilizer (MulAut (matrixProjectiveDerived Q)) Y

theorem mem_familyOrbitKernel_iff (α : MulAut (matrixProjectiveDerived Q)) :
    α ∈ familyOrbitKernel Q ↔
      ∀ Y ∈ MulAction.orbit (MulAut (matrixProjectiveDerived Q)) (projectivePointFamily Q),
        α • Y = Y := by
  simp only [familyOrbitKernel, Subgroup.mem_iInf, MulAction.mem_stabilizer_iff]

theorem familyOrbitKernel_normal : (familyOrbitKernel Q).Normal := by
  constructor
  intro α hα β
  rw [mem_familyOrbitKernel_iff] at hα ⊢
  intro Y hY
  have hY' : β⁻¹ • Y ∈ MulAction.orbit (MulAut (matrixProjectiveDerived Q))
      (projectivePointFamily Q) := MulAction.mem_orbit_of_mem_orbit β⁻¹ hY
  rw [mul_smul, mul_smul, hα _ hY', smul_inv_smul]

theorem familyOrbitKernel_le : familyOrbitKernel Q ≤ projectivePointFamilyAut Q := fun α hα =>
  (mem_familyOrbitKernel_iff Q α).mp hα _ (MulAction.mem_orbit_self _)

@[expose] def OrthogonalGates (f : ℕ) : Prop :=
  (∀ g : similarityPairs Q, matrixProjectiveConjugationHom Q g = 1 ↔
    g.val.right = 1 ∧ ∃ a : Kˣ, g.val.left = GeneralLinearGroup.scalar (Fin d) a) ∧
  (∃ ψ : matrixProjectiveImage Q →* (K ≃+* K),
    (∀ g : similarityPairs Q, ψ ⟨matrixProjectiveConjugationHom Q g, ⟨g, rfl⟩⟩ = g.val.right) ∧
    ψ.ker = (linearConjugationHom Q).range.subgroupOf (matrixProjectiveImage Q) ∧
    IsCyclic ψ.range) ∧
  (OuterAutomorphisms.inner (matrixProjectiveDerived Q) ≤ (linearConjugationHom Q).range ∧
    ∃ k : ℕ, (OuterAutomorphisms.inner (matrixProjectiveDerived Q)).relIndex
      (linearConjugationHom Q).range = 2 ^ k) ∧
  (MulAction.orbit (MulAut (matrixProjectiveDerived Q)) (projectivePointFamily Q)).ncard ≤ 3 ∧
  familyOrbitKernel Q ≤ projectivePointFamilyAut Q ∧
  projectivePointFamilyAut Q = matrixProjectiveImage Q ∧
  (∀ p : ℕ, p.Prime → 3 < p → ∀ A : Subgroup (MulAut (matrixProjectiveDerived Q)),
    IsPGroup p A → A ≤ familyOrbitKernel Q) ∧
  (∀ p : ℕ, p.Prime → 3 < p → ∀ A : Subgroup (MulAut (matrixProjectiveDerived Q)),
    CFSG.IsElementaryAbelian p A → Nat.card A = p ^ 2 →
    ¬ A ≤ OuterAutomorphisms.inner (matrixProjectiveDerived Q) →
    Nat.card (A ⊓ OuterAutomorphisms.inner (matrixProjectiveDerived Q) : Subgroup _) = p ∧ p ∣ f ∧
      2 ^ p ≤ Nat.card K) ∧
  ∀ p : ℕ, p.Prime → 3 < p → ∀ A S : Subgroup (MulAut (matrixProjectiveDerived Q)),
    IsPGroup p A → Group.IsSolvable S → ¬ p ∣ Nat.card S →
    A ≤ Subgroup.normalizer (S : Set (MulAut (matrixProjectiveDerived Q))) →
    ⁅S, A⁆ ≤ (linearConjugationHom Q).range

theorem matrixProjectiveConjugationHom_eq_one_iff (hnd : Q.polarBilin.Nondegenerate)
    (hS3 : ∃ S : Submodule K (Fin d → K), Module.finrank K S = 3 ∧ ∀ v ∈ S, Q v = 0)
    (hAP : CFSG.ComponentClassification.CatalogueBOrthogonalPointAction.ActionProperties Q
      (projectivePointAction Q)) (g : similarityPairs Q) :
    matrixProjectiveConjugationHom Q g = 1 ↔
      g.val.right = 1 ∧ ∃ a : Kˣ, g.val.left = GeneralLinearGroup.scalar (Fin d) a := by
  constructor
  · intro hg
    have hcomm : ∀ x, similarityPointAction Q g * projectivePointAction Q x =
        projectivePointAction Q x * similarityPointAction Q g := fun x => by
      have h := similarity_projective_covariance Q g x
      rw [hg, MulAut.one_apply, mul_inv_eq_iff_eq_mul] at h
      exact h
    have hinj := hAP.2.2.2.2.2.1
    have hη : similarityPointAction Q g = 1 := by
      ext L
      have h1 : CFSG.ComponentClassification.CatalogueBOrthogonalPointAction.actionStabilizer Q
          (projectivePointAction Q) (similarityPointAction Q g L) =
          CFSG.ComponentClassification.CatalogueBOrthogonalPointAction.actionStabilizer Q
            (projectivePointAction Q) L := by
        ext x
        change projectivePointAction Q x (similarityPointAction Q g L) =
          similarityPointAction Q g L ↔ projectivePointAction Q x L = L
        rw [← Equiv.Perm.mul_apply, ← hcomm, Equiv.Perm.mul_apply,
          (similarityPointAction Q g).injective.eq_iff]
      exact hinj h1
    obtain ⟨h1, a, ha⟩ := (similarityPointAction_eq_one_iff Q hnd hS3 g).mp hη
    exact ⟨h1, a, ha.symm⟩
  · rintro ⟨h1, a, ha⟩
    rw [← map_one (matrixProjectiveConjugationHom Q)]
    refine matrixProjectiveConjugationHom_eq_of_left_eq_mul_scalar Q (g := g) (h := 1) a ?_ h1
    rw [ha]
    exact (one_mul _).symm

theorem matrixProjectiveConjugationHom_not_mem_range_isometry
    (hnd : Q.polarBilin.Nondegenerate)
    (hS3 : ∃ S : Submodule K (Fin d → K), Module.finrank K S = 3 ∧ ∀ v ∈ S, Q v = 0)
    (hAP : CFSG.ComponentClassification.CatalogueBOrthogonalPointAction.ActionProperties Q
      (projectivePointAction Q)) {g : similarityPairs Q} (hg : g.val.right ≠ 1) :
    matrixProjectiveConjugationHom Q g ∉ (isometryConjugationHom Q).range := by
  rintro ⟨A, hA⟩
  have h1 : matrixProjectiveConjugationHom Q (g * (matrixIsometryInclusion Q A)⁻¹) = 1 := by
    rw [map_mul, map_inv]
    change matrixProjectiveConjugationHom Q g * (isometryConjugationHom Q A)⁻¹ = 1
    rw [hA, mul_inv_cancel]
  have h2 := ((matrixProjectiveConjugationHom_eq_one_iff Q hnd hS3 hAP _).1 h1).1
  apply hg
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, SemidirectProduct.mul_right,
    SemidirectProduct.inv_right, matrixIsometryInclusion_val, SemidirectProduct.right_inl,
    inv_one, mul_one] using h2

theorem orthogonalGates_of [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hQ : Q ≠ 0) (hnd : Q.polarBilin.Nondegenerate)
    (hS3 : ∃ S : Submodule K (Fin d → K), Module.finrank K S = 3 ∧ ∀ v ∈ S, Q v = 0)
    (hAP : CFSG.ComponentClassification.CatalogueBOrthogonalPointAction.ActionProperties Q
      (projectivePointAction Q))
    (hab : ∃ a : ℕ, Nat.card (Abelianization (matrixIsometries Q)) = 2 ^ a)
    (hEA : projectivePointFamilyAut Q = matrixProjectiveImage Q)
    (hX : (MulAction.orbit (MulAut (matrixProjectiveDerived Q))
      (projectivePointFamily Q)).ncard ≤ 3) :
    OrthogonalGates Q f := by
  classical
  have hQv := exists_nonzero_value Q hQ
  set κ := matrixProjectiveConjugationHom Q with hκ
  set E := matrixProjectiveImage Q with hEdef
  set D := (linearConjugationHom Q).range with hDdef
  set H := OuterAutomorphisms.inner (matrixProjectiveDerived Q) with hHdef
  have hker := matrixProjectiveConjugationHom_eq_one_iff Q hnd hS3 hAP
  have hright : ∀ g h : similarityPairs Q, κ g = κ h → g.val.right = h.val.right := by
    intro g h hgh
    have h1 : κ (h⁻¹ * g) = 1 := by rw [map_mul, map_inv, hgh, inv_mul_cancel]
    have h2 := ((hker _).mp h1).1
    have h3 : (h⁻¹ * g).val.right = h.val.right⁻¹ * g.val.right := rfl
    rw [h3, inv_mul_eq_one] at h2
    exact h2.symm
  have hmemD : ∀ g : similarityPairs Q, κ g ∈ D ↔ g.val.right = 1 := by
    intro g
    constructor
    · rintro ⟨h, hh⟩
      rw [← hright _ _ hh]
      exact (mem_linearSimilarityPairs_iff Q h.val).mp h.2
    · intro hg
      exact ⟨⟨g, (mem_linearSimilarityPairs_iff Q g).mpr hg⟩, rfl⟩
  have hDE : D ≤ E := by
    rintro _ ⟨g, rfl⟩
    exact ⟨g.val, rfl⟩
  have hκker_le : κ.ker ≤ (fieldProjection Q).ker := fun g hg =>
    ((hker g).mp (MonoidHom.mem_ker.mp hg)).1
  set ψ : matrixProjectiveImage Q →* (K ≃+* K) :=
    (QuotientGroup.lift κ.ker (fieldProjection Q) hκker_le).comp
      (QuotientGroup.quotientKerEquivRange κ).symm.toMonoidHom with hψdef
  have hψ : ∀ g : similarityPairs Q, ψ ⟨κ g, ⟨g, rfl⟩⟩ = g.val.right := by
    intro g
    have e1 : (QuotientGroup.quotientKerEquivRange κ).symm ⟨κ g, ⟨g, rfl⟩⟩ =
        (g : similarityPairs Q ⧸ κ.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    change QuotientGroup.lift κ.ker (fieldProjection Q) hκker_le
      ((QuotientGroup.quotientKerEquivRange κ).symm ⟨κ g, ⟨g, rfl⟩⟩) = g.val.right
    rw [e1, QuotientGroup.lift_mk]
    rfl
  have hψker : ψ.ker = D.subgroupOf E := by
    ext ⟨α, g, rfl⟩
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hψ]
    exact (hmemD g).symm
  have : IsCyclic (K ≃+* K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  have hEab : ∀ x ∈ E, ∀ y ∈ E, ⁅x, y⁆ ∈ D := by
    rintro _ ⟨g, rfl⟩ _ ⟨h, rfl⟩
    rw [← map_commutatorElement, hmemD]
    change ⁅g.val.right, h.val.right⁆ = 1
    rw [commutatorElement_eq_one_iff_mul_comm]
    have hc : IsMulCommutative (K ≃+* K) := IsCyclic.isMulCommutative
    exact hc.is_comm.comm _ _
  have hIO : H ≤ (isometryConjugationHom Q).range := by
    rw [hHdef, inner_eq_map_commutator Q]
    exact Subgroup.map_le_range _ _
  have hOD := isometryConjugationHom_range_le Q
  have hHD : H ≤ D := hIO.trans hOD
  have h2grp : ∃ k : ℕ, H.relIndex D = 2 ^ k := by
    rw [← Subgroup.relIndex_mul_relIndex _ _ _ hIO hOD]
    obtain ⟨a, ha⟩ := hab
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (ha ▸ relIndex_inner_dvd Q)
    have hsq : (powMonoidHom 2 : Kˣ →* Kˣ).range.index ∣ 2 ^ 1 := by
      rw [IsCyclic.index_powMonoidHom_range, pow_one]
      exact Nat.gcd_dvd_right _ _
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      ((relIndex_isometryRange_dvd Q hQv).trans hsq)
    exact ⟨i + j, by rw [hi, hj, pow_add]⟩
  have hpK₀ : ∀ p : ℕ, p.Prime → 3 < p → ∀ A : Subgroup (MulAut (matrixProjectiveDerived Q)),
      IsPGroup p A → A ≤ familyOrbitKernel Q := by
    intro p hp hp3 A hA a ha
    have : Fact p.Prime := ⟨hp⟩
    rw [mem_familyOrbitKernel_iff]
    intro Y hY
    have hsub : MulAction.orbit A Y ⊆
        MulAction.orbit (MulAut (matrixProjectiveDerived Q)) (projectivePointFamily Q) := by
      rintro _ ⟨b, rfl⟩
      exact MulAction.mem_orbit_of_mem_orbit (b : MulAut (matrixProjectiveDerived Q)) hY
    have hle : (MulAction.stabilizer A Y).index ≤ 3 := by
      rw [MulAction.index_stabilizer]
      exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans hX
    obtain ⟨k, hk⟩ := hA.exists_card_eq
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp
      (hk ▸ Subgroup.index_dvd_card (MulAction.stabilizer A Y))
    have hj0 : j = 0 := by
      by_contra hne
      have := Nat.le_self_pow hne p
      omega
    rw [hj0, pow_zero, Subgroup.index_eq_one] at hj
    have hmem : (⟨a, ha⟩ : A) ∈ MulAction.stabilizer A Y := hj ▸ Subgroup.mem_top _
    exact hmem
  have hK₀E : familyOrbitKernel Q ≤ E := (familyOrbitKernel_le Q).trans hEA.le
  have : H.Normal := OuterAutomorphisms.inner_normal _
  have hplane : ∀ p : ℕ, p.Prime → 3 < p → ∀ A : Subgroup (MulAut (matrixProjectiveDerived Q)),
      CFSG.IsElementaryAbelian p A → Nat.card A = p ^ 2 → ¬ A ≤ H →
      Nat.card (A ⊓ H : Subgroup _) = p ∧ p ∣ f ∧ 2 ^ p ≤ Nat.card K := by
    intro p hp hp3 A hAe hAcard hAH
    have : Fact p.Prime := ⟨hp⟩
    have := hAe
    have hAp : IsPGroup p A := CFSG.IsElementaryAbelian.isPGroup p A
    have hAE : A ≤ E := (hpK₀ p hp hp3 A hAp).trans hK₀E
    have hcop2 : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr (by omega)
    have hADH : A ⊓ D ≤ H := by
      rintro x ⟨hxA, hxD⟩
      obtain ⟨k₂, hk₂⟩ := h2grp
      obtain ⟨k, hk⟩ := hAp ⟨x, hxA⟩
      set y : D := ⟨x, hxD⟩ with hydef
      have hy : y ^ (p ^ k) = 1 := Subtype.ext (by
        have := congrArg Subtype.val hk
        simpa using this)
      have h1 : orderOf (y : D ⧸ H.subgroupOf D) ∣ p ^ k :=
        orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hy, QuotientGroup.mk_one])
      have h2 : orderOf (y : D ⧸ H.subgroupOf D) ∣ 2 ^ k₂ := by
        rw [← hk₂, Subgroup.relIndex, Subgroup.index_eq_card]
        exact orderOf_dvd_natCard _
      have h3 : orderOf (y : D ⧸ H.subgroupOf D) = 1 :=
        Nat.Coprime.eq_one_of_dvd ((Nat.Coprime.pow k k₂ hcop2).coprime_dvd_left h1) h2
      rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
      exact h3
    set φ : A →* (K ≃+* K) := ψ.comp (Subgroup.inclusion hAE) with hφ
    have hφker : φ.ker = D.subgroupOf A := by
      ext a
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hφ, MonoidHom.comp_apply, ← MonoidHom.mem_ker,
        hψker, Subgroup.mem_subgroupOf]
      rfl
    have hφp : ∀ a : A, φ a ^ p = 1 := by
      intro a
      rw [← map_pow]
      have ha : a ^ p = 1 :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (CFSG.IsElementaryAbelian.exponent_dvd_p p A) a
      rw [ha, map_one]
    have hrange_dvd : Nat.card φ.range ∣ p := by
      rw [← IsCyclic.exponent_eq_card]
      refine Monoid.exponent_dvd_of_forall_pow_eq_one fun σ => ?_
      obtain ⟨a, ha⟩ := σ.2
      apply Subtype.ext
      rw [SubgroupClass.coe_pow, ← ha, hφp, OneMemClass.coe_one]
    have hrange_ne : Nat.card φ.range ≠ 1 := by
      intro h1
      apply hAH
      intro x hx
      apply hADH
      refine ⟨hx, ?_⟩
      have hmem : (⟨x, hx⟩ : A) ∈ φ.ker := by
        rw [MonoidHom.mem_ker]
        have hbot : φ.range = ⊥ := Subgroup.card_eq_one.mp h1
        have : φ ⟨x, hx⟩ ∈ φ.range := ⟨⟨x, hx⟩, rfl⟩
        rw [hbot, Subgroup.mem_bot] at this
        exact this
      rw [hφker, Subgroup.mem_subgroupOf] at hmem
      exact hmem
    have hrange : Nat.card φ.range = p := ((Nat.dvd_prime hp).mp hrange_dvd).resolve_left hrange_ne
    have hkercard : Nat.card φ.ker = p := by
      have h1 := Subgroup.card_mul_index φ.ker
      rw [Subgroup.index_ker, hrange, hAcard, sq] at h1
      exact Nat.eq_of_mul_eq_mul_right hp.pos h1
    have hAHeq : A ⊓ H = A ⊓ D := le_antisymm (inf_le_inf_left _ hHD) (le_inf inf_le_left hADH)
    have hcardAD : Nat.card (A ⊓ D : Subgroup _) = p := by
      rw [← hkercard, hφker, inf_comm, ← Subgroup.subgroupOf_map_subtype,
        Subgroup.card_map_of_injective A.subtype_injective]
    refine ⟨by rw [hAHeq, hcardAD], ?_, ?_⟩
    · obtain ⟨-, -, -, -, -, hdvd⟩ := finite_field_automorphism_fixed_field_cardinality hℓ hf hK
      exact hrange ▸ (hdvd φ.range).1
    · obtain ⟨-, -, -, -, -, hdvd⟩ := finite_field_automorphism_fixed_field_cardinality hℓ hf hK
      have hpf : p ∣ f := hrange ▸ (hdvd φ.range).1
      have hfp : p ≤ f := Nat.le_of_dvd (by omega) hpf
      rw [hK]
      calc 2 ^ p ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hfp
        _ ≤ ℓ ^ f := Nat.pow_le_pow_left hℓ.two_le f
  have hcap : ∀ p : ℕ, p.Prime → 3 < p → ∀ A S : Subgroup (MulAut (matrixProjectiveDerived Q)),
      IsPGroup p A → Group.IsSolvable S → ¬ p ∣ Nat.card S →
      A ≤ Subgroup.normalizer (S : Set (MulAut (matrixProjectiveDerived Q))) → ⁅S, A⁆ ≤ D := by
    intro p hp hp3 A S hA _ hpS hAN
    have hAK₀ := hpK₀ p hp hp3 A hA
    have hK₀n := familyOrbitKernel_normal Q
    have hRK₀ : ⁅S, A⁆ ≤ familyOrbitKernel Q := by
      rw [Subgroup.commutator_le]
      intro s _ a ha
      rw [commutatorElement_def]
      exact mul_mem (hK₀n.conj_mem a (hAK₀ ha) s) (inv_mem (hAK₀ ha))
    have hidem := CFSG.LargeEvenClassification.Helpers.coprime_normalized_commutator_idempotent
      hp A S hA hpS hAN
    rw [← hidem, Subgroup.commutator_le]
    intro r hr a ha
    exact hEab r (hK₀E (hRK₀ hr)) a (hK₀E (hAK₀ ha))
  exact ⟨hker, ⟨ψ, hψ, hψker, inferInstance⟩, ⟨hHD, h2grp⟩, hX, familyOrbitKernel_le Q, hEA,
    hpK₀, hplane, hcap⟩

theorem orbit_ncard_le_three_of_top
    (h : projectivePointFamilyAut Q = ⊤) :
    (MulAction.orbit (MulAut (matrixProjectiveDerived Q)) (projectivePointFamily Q)).ncard ≤ 3 := by
  have h1 : (projectivePointFamilyAut Q).index =
      (MulAction.orbit (MulAut (matrixProjectiveDerived Q)) (projectivePointFamily Q)).ncard :=
    MulAction.index_stabilizer _ _
  rw [← h1, h, Subgroup.index_top]
  norm_num

theorem exists_card_abelianization_eq_two_pow [Finite K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (e : ι ≃ Fin d) (Q₀ : QuadraticForm K (ι → K))
    (h : CFSG.IsElementaryAbelian 2 (Abelianization (TauCeti.QuadraticMap.orthogonalGroup Q₀))) :
    ∃ a : ℕ, Nat.card (Abelianization (matrixIsometries (reindexQuadraticForm e Q₀))) = 2 ^ a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite ((ι → K) ≃ₗ[K] (ι → K)) := Finite.of_injective
    (fun g : (ι → K) ≃ₗ[K] (ι → K) => (g : (ι → K) → (ι → K)))
    fun g g' hg => LinearEquiv.ext (congrFun hg)
  have : Finite (Abelianization (TauCeti.QuadraticMap.orthogonalGroup Q₀)) :=
    Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  rw [card_abelianization_matrixIsometries_reindex]
  exact (CFSG.IsElementaryAbelian.isPGroup 2 _).exists_card_eq

end General


section Models

open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
  (orthogonal_geometry_plus_point_family_orbit)
open CFSG.LieType.Universal.Spin

@[expose] def ModelOrthogonalGates (G : Type) [Group G] (t : StatedLieTag) (n ℓ f : ℕ) : Prop :=
  match t with
  | .POmegaOdd => ∀ (K : Type) [Field K] [Finite K], Nat.card K = ℓ ^ f →
      G ≃* StatedProj (StatedOmega (StatedQuadOdd n K)) →
        OrthogonalGates (coordinateQuadOdd n K) f
  | .POmegaPlus => ∀ (K : Type) [Field K] [Finite K], Nat.card K = ℓ ^ f →
      G ≃* StatedProj (StatedOmega (StatedQuadPlus n K)) →
        OrthogonalGates (coordinateQuadPlus n K) f
  | .POmegaMinus => ∀ (hn : 1 ≤ n) (K : Type) [Field K] [Finite K], Nat.card K = ℓ ^ f →
      ∀ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
      G ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c)) →
        OrthogonalGates (coordinateQuadMinus n K hn b c) f
  | _ => False

theorem orthogonal_large_prime_semilinear_field_and_diagonal_gates (G : Type) [Group G]
    (c : StatedLieTag) (hc : c = .POmegaOdd ∨ c = .POmegaPlus ∨ c = .POmegaMinus) (n ℓ f : ℕ)
    (h : StatedClassicalModel G c n ℓ f) : ModelOrthogonalGates G c n ℓ f := by
  rcases hc with rfl | rfl | rfl
  ·
    intro K _ _ hK e
    obtain ⟨hℓ, hf, -, -⟩ := h.1
    obtain ⟨-, hnd, hT, -, hAP, -⟩ := coordinate_model_witness_odd h K hK e
    have hQ := (coordinate_model_intrinsic_odd h K hK e).1
    have hab := orthogonal_model_isometry_abelianization_order_bound G .POmegaOdd (.inl rfl)
      n ℓ f h K hK (quadOdd n K) (coe_quadOdd n K) e
    have hEA := ((orthogonal_geometry_model_stabilizer_preserving_image G .POmegaOdd (.inl rfl)
      n ℓ f h) K hK e).1
    have htop := ((OrthogonalTail.orthogonal_geometry_tail_model_point_family_invariant G
      .POmegaOdd (.inl rfl) n ℓ f h) K hK).2
    exact orthogonalGates_of _ hℓ hf hK hQ hnd hT hAP
      (exists_card_abelianization_eq_two_pow (oddIndexEquiv n) (quadOdd n K) hab.1) hEA
      (orbit_ncard_le_three_of_top _ htop)
  ·
    intro K _ _ hK e
    obtain ⟨hℓ, hf, hn⟩ := h.1
    obtain ⟨-, hnd, hT, -, hAP, -⟩ := coordinate_model_witness_plus h K hK e
    have hQ := (coordinate_model_intrinsic_plus h K hK e).1
    have hab := orthogonal_model_isometry_abelianization_order_bound G .POmegaPlus
      (.inr (.inl rfl)) n ℓ f h K hK (quadPlus n K) (coe_quadPlus n K) e
    have hEA := ((orthogonal_geometry_model_stabilizer_preserving_image G .POmegaPlus
      (.inr (.inl rfl)) n ℓ f h) K hK e).1
    have horbit := orthogonal_geometry_plus_point_family_orbit h hK e
    have hX : (MulAction.orbit (MulAut (matrixProjectiveDerived (coordinateQuadPlus n K)))
        (projectivePointFamily (coordinateQuadPlus n K))).ncard ≤ 3 := by
      rcases (show n = 4 ∨ 5 ≤ n by omega) with h4 | h5
      · exact (horbit.2.2.2.2.2 h4).2
      · exact orbit_ncard_le_three_of_top _ (horbit.2.2.2.2.1 h5)
    exact orthogonalGates_of _ hℓ hf hK hQ hnd hT hAP
      (exists_card_abelianization_eq_two_pow (plusIndexEquiv n) (quadPlus n K) hab.1) hEA hX
  ·
    intro hn1 K _ _ hK b c hirr e
    obtain ⟨hℓ, hf, -⟩ := h.1
    obtain ⟨-, hnd, hT, -, hAP, -⟩ := coordinate_model_witness_minus h K hK b c hirr e
    have hQ := (coordinate_model_intrinsic_minus h K hK b c hirr e).1
    have hab := orthogonal_model_isometry_abelianization_order_bound G .POmegaMinus
      (.inr (.inr rfl)) n ℓ f h K hK b c hirr (quadMinus n K b c) (coe_quadMinus n K b c) e
    have hEA := ((orthogonal_geometry_model_stabilizer_preserving_image G .POmegaMinus
      (.inr (.inr rfl)) n ℓ f h) hn1 K hK b c hirr e).1
    have htop := ((OrthogonalTail.orthogonal_geometry_tail_model_point_family_invariant G
      .POmegaMinus (.inr rfl) n ℓ f h) hn1 K hK b c hirr).2
    exact orthogonalGates_of _ hℓ hf hK hQ hnd hT hAP
      (exists_card_abelianization_eq_two_pow (minusIndexEquiv n hn1) (quadMinus n K b c) hab.1)
      hEA (orbit_ncard_le_three_of_top _ htop)

end Models

end CFSG.RankThree.Classical.SteinbergBY
