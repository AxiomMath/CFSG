module

public import CFSG.RankThree.PartTwo.KFacts.AutKindsStd
public import CFSG.RankThree.PartTwo.KFacts.AutKindsCentral
import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneLinearField

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

section Linear

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {n : ℕ} {K : Type*} [Field K]

theorem fieldAut_mem_linearAutGroup_iff [Finite K] (hn : 3 ≤ n) {σ : K ≃+* K} :
    fieldAut n K σ ∈ linearAutGroup n K ↔ σ = 1 := by
  constructor
  · intro hmem
    obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.mp hmem
    have h1 : conjAut n K A⁻¹ * fieldAut n K σ = 1 := by rw [map_inv, hA, inv_mul_cancel]
    exact (eq_one_of_conjAut_mul_fieldAut_eq_one hn _ _ h1).1
  · rintro rfl
    rw [map_one]
    exact one_mem _

theorem stdPinnedPSL_separated [Finite K] (hn : 3 ≤ n) : (stdPinnedPSL n K).Separated := by
  have hnormR : ∀ r ∈ standardFieldGraph n K, ∀ d ∈ linearAutGroup n K,
      r * d * r⁻¹ ∈ linearAutGroup n K := fun r hr d hd =>
    (Subgroup.mem_normalizer_iff.mp (standardFieldGraph_le_normalizer hr) d).mp hd
  have hinter : ∀ φ ∈ (stdPinnedPSL n K).field, φ ∈ (stdPinnedPSL n K).inndiag → φ = 1 := by
    rintro _ ⟨σ, rfl⟩ hmem
    rw [(fieldAut_mem_linearAutGroup_iff hn).mp hmem, map_one]
  refine ⟨?_, ?_, hinter, ?_, ?_⟩
  · rintro _ ⟨σ, rfl⟩ d hd
    exact hnormR _ (fieldAut_mem_standardFieldGraph σ) d hd
  · intro γ hγ d hd
    rw [stdPinnedPSL_graph, Set.mem_singleton_iff] at hγ
    subst hγ
    exact hnormR _ dualAut_mem_standardFieldGraph d hd
  · intro γ hγ _ d hd _ ⟨σ, hσ⟩ heq
    rw [stdPinnedPSL_graph, Set.mem_singleton_iff] at hγ
    subst hγ
    apply ProjectivePlane.dualAut_not_mem_semilinearAutGroup (K := K) hn
    rw [heq, ← hσ]
    exact mul_mem (linearAutGroup_le_semilinearAutGroup hd) (fieldAut_mem_semilinearAutGroup σ)
  · intro γ hγ γ' hγ' φ hφ hφ1 d hd heq
    rw [stdPinnedPSL_graph, Set.mem_singleton_iff] at hγ hγ'
    subst hγ
    subst hγ'
    refine hφ1 (hinter φ hφ ?_)
    have hφ' : φ = (dualAut n K)⁻¹ * d⁻¹ * (dualAut n K)⁻¹⁻¹ := by
      calc φ = (d * dualAut n K)⁻¹ * (d * (dualAut n K * φ)) := by group
        _ = (d * dualAut n K)⁻¹ * dualAut n K := by rw [← heq]
        _ = (dualAut n K)⁻¹ * d⁻¹ * (dualAut n K)⁻¹⁻¹ := by group
    rw [hφ']
    exact hnormR _ (inv_mem dualAut_mem_standardFieldGraph) _ (inv_mem hd)

end Linear

section LinearTwo

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo

variable {K : Type*} [Field K]

theorem stdPinnedPSL2_separated [Finite K] : (stdPinnedPSL2 K).Separated := by
  refine PinnedAut.Separated.of_graph_eq_empty _ rfl ?_ ?_
  · rintro _ ⟨σ, rfl⟩ _ ⟨g, rfl⟩
    exact ⟨_, (psl2FieldAut_mul_pglAction_mul_inv σ g).symm⟩
  · rintro _ ⟨σ, rfl⟩ ⟨g, hg⟩
    have h1 : semilinearAction K (SemidirectProduct.inl g) =
        semilinearAction K (SemidirectProduct.inr σ) := by
      rw [semilinearAction_inl, semilinearAction_inr, hg]
    have h2 := congrArg SemidirectProduct.right (semilinearAction_injective K h1)
    rw [SemidirectProduct.right_inl, SemidirectProduct.right_inr] at h2
    rw [← h2, map_one]

end LinearTwo

section Unitary

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem stdPinnedPSU3_separated : (stdPinnedPSU3 h).Separated := by
  refine PinnedAut.Separated.of_graph_eq_empty _ rfl ?_ ?_
  · rintro _ ⟨σ, rfl⟩ _ ⟨A, rfl⟩
    exact ⟨_, (psuField_mul_psuConj_mul_inv σ A).symm⟩
  · rintro _ ⟨σ, rfl⟩ hmem
    rw [psuField_mem_range_psuConj_iff.mp hmem, map_one]

end Unitary

section Symplectic

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

variable {r : ℕ} {K : Type} [Field K]

theorem stdPinnedPSp_separated [Finite K] (hr : 1 ≤ r) : (stdPinnedPSp r K).Separated := by
  refine PinnedAut.Separated.of_graph_eq_empty _ rfl ?_ ?_
  · rintro _ ⟨σ, rfl⟩ _ ⟨A, rfl⟩
    exact ⟨_, (fieldAut_mul_conjAut_mul_inv σ A).symm⟩
  · rintro _ ⟨σ, rfl⟩ hmem
    rw [(fieldAut_mem_range_conjAut_iff hr).mp hmem, map_one]

end Symplectic

section Suzuki

open CFSG.Blueprint
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut)

variable {a : ℕ} {K : Type} [Field K]

theorem stdPinnedSz_separated (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (stdPinnedSz a K).Separated := by
  obtain ⟨-, -, -, hinf, -⟩ :=
    CFSG.RankThree.Automorphisms.Suzuki_full_field_automorphism_splitting a ha K hK
  refine PinnedAut.Separated.of_graph_eq_empty _ rfl ?_ ?_
  · rintro _ ⟨σ, rfl⟩ _ ⟨g, rfl⟩
    exact ⟨_, (mul_mulAutConj_mul_inv _ g).symm⟩
  · rintro φ hφ hmem
    have h1 : φ ∈ (szFieldAut a K).range ⊓
        CFSG.ComponentClassification.OuterAutomorphisms.inner (suzukiGroup a K) := ⟨hφ, hmem⟩
    rw [hinf] at h1
    exact h1

end Suzuki

section Induced

variable {G : Type*} [Group G] [Finite G] (L : Subgroup G)

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem inducesKindPSL_unique {n : ℕ} {K : Type*} [Field K] [Finite K] (hn : 3 ≤ n) {x : G}
    {k₁ k₂ : AutKind} (h₁ : InducesKindPSL n K L x k₁) (h₂ : InducesKindPSL n K L x k₂) :
    k₁ = k₂ := by
  obtain ⟨e, h₁⟩ := h₁
  exact InducesKind.unique L (stdPinnedPSL_separated hn) h₁
    ((inducesKindPSL_iff L hn e x k₂).mp h₂)

theorem inducesKindSL_unique {n : ℕ} {K : Type*} [Field K] [Finite K] (hn : 3 ≤ n) {x : G}
    {k₁ k₂ : AutKind} (h₁ : InducesKindSL n K L x k₁) (h₂ : InducesKindSL n K L x k₂) :
    k₁ = k₂ := by
  obtain ⟨e, hx, h₁⟩ := h₁
  obtain ⟨hx', h₂⟩ := (inducesKindSL_iff L hn e x k₂).mp h₂
  exact (stdPinnedPSL_separated hn).hasKind_unique h₁ h₂

theorem inducesKindPSL2_unique {K : Type*} [Field K] [Finite K] {x : G} {k₁ k₂ : AutKind}
    (h₁ : InducesKindPSL2 K L x k₁) (h₂ : InducesKindPSL2 K L x k₂) : k₁ = k₂ := by
  obtain ⟨e, h₁⟩ := h₁
  exact InducesKind.unique L stdPinnedPSL2_separated h₁ ((inducesKindPSL2_iff L e x k₂).mp h₂)

theorem inducesKindPSU3_unique {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}
    (hq : 2 < p ^ f) {x : G} {k₁ k₂ : AutKind} (h₁ : InducesKindPSU3 h L x k₁)
    (h₂ : InducesKindPSU3 h L x k₂) : k₁ = k₂ := by
  obtain ⟨e, h₁⟩ := h₁
  exact InducesKind.unique L (stdPinnedPSU3_separated h) h₁
    ((inducesKindPSU3_iff L hq e x k₂).mp h₂)

theorem inducesKindSU3_unique {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}
    (hq : 2 < p ^ f) {x : G} {k₁ k₂ : AutKind} (h₁ : InducesKindSU3 h L hq x k₁)
    (h₂ : InducesKindSU3 h L hq x k₂) : k₁ = k₂ := by
  obtain ⟨e, hx, h₁⟩ := h₁
  obtain ⟨hx', h₂⟩ := (inducesKindSU3_iff L hq e x k₂).mp h₂
  exact (stdPinnedPSU3_separated h).hasKind_unique h₁ h₂

theorem inducesKindPSp_unique {r : ℕ} {K : Type} [Field K] [Finite K] (hr : 3 ≤ r) {x : G}
    {k₁ k₂ : AutKind} (h₁ : InducesKindPSp r K L x k₁) (h₂ : InducesKindPSp r K L x k₂) :
    k₁ = k₂ := by
  obtain ⟨e, h₁⟩ := h₁
  exact InducesKind.unique L (stdPinnedPSp_separated (by omega)) h₁
    ((inducesKindPSp_iff L hr e x k₂).mp h₂)

theorem inducesKindSz_unique {a : ℕ} {K : Type} [Field K] (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {x : G} {k₁ k₂ : AutKind}
    (h₁ : InducesKindSz a K L x k₁) (h₂ : InducesKindSz a K L x k₂) : k₁ = k₂ := by
  obtain ⟨e, h₁⟩ := h₁
  exact InducesKind.unique L (stdPinnedSz_separated ha hK) h₁
    ((inducesKindSz_iff L ha hK e x k₂).mp h₂)

theorem InducesStdKind.inducesOuterTheta {x : G} {k : AutKind} (h : InducesStdKind L x k)
    (hk : k ≠ .inner) : InducesOuterTheta x L := by
  cases h with
  | psl2 K h =>
    obtain ⟨e, h⟩ := h
    exact InducesKind.inducesOuterTheta L stdPinnedPSL2_separated h hk
  | psl n K hn h =>
    obtain ⟨e, h⟩ := h
    exact InducesKind.inducesOuterTheta L (stdPinnedPSL_separated hn) h hk
  | sl n K hn h =>
    obtain ⟨e, hx, h⟩ := h
    refine (not_isInnerAut_inducedAutHom_iff L e hx).mp fun hin => ?_
    exact (stdPinnedPSL_separated hn).not_isInnerAut_of_hasKind h hk (isInnerAut_descendAut hin)
  | psu3 hK hq h =>
    obtain ⟨e, h⟩ := h
    exact InducesKind.inducesOuterTheta L (stdPinnedPSU3_separated hK) h hk
  | su3 hK hq h =>
    obtain ⟨e, hx, h⟩ := h
    refine (not_isInnerAut_inducedAutHom_iff L e hx).mp fun hin => ?_
    exact (stdPinnedPSU3_separated hK).not_isInnerAut_of_hasKind h hk
      (isInnerAut_congr_centerDescend _ hin)
  | psp r K hr h =>
    obtain ⟨e, h⟩ := h
    exact InducesKind.inducesOuterTheta L
      (stdPinnedPSp_separated (by rcases hr with hr | ⟨hr, -⟩ <;> omega)) h hk
  | psp4even F h =>
    obtain ⟨e, h⟩ := h
    exact InducesKind.inducesOuterTheta L stdPinnedPSp4Even_separated h hk
  | g2 K hK3 hK4 h =>
    obtain ⟨e, h⟩ := h
    exact InducesKind.inducesOuterTheta L (stdPinnedG2_separated hK3 hK4) h hk
  | sz a K ha hK h =>
    obtain ⟨e, h⟩ := h
    exact InducesKind.inducesOuterTheta L (stdPinnedSz_separated ha hK) h hk
  | triality f hf K hK σ hσ h => exact h.inducesOuterTheta L hf hK hσ hk
  | largeRee a ha K hK h => exact h.inducesOuterTheta L ha hK hk

theorem not_inducesStdKind_of_not_inducesOuterTheta {x : G} (hx : ¬ InducesOuterTheta x L)
    {k : AutKind} (hk : k ≠ .inner) : ¬ InducesStdKind L x k :=
  fun h => hx (h.inducesOuterTheta L hk)

omit [Finite G] in
theorem not_inducesOuterTheta_one [Finite G] : ¬ InducesOuterTheta (1 : G) L := by
  rintro ⟨hx, h⟩
  apply h
  have h1 : (⟨1, hx⟩ : Subgroup.normalizer (L : Set G)) = 1 := rfl
  rw [h1, map_one, map_one]
  exact ⟨1, map_one _⟩

theorem not_inducesStdKind_one {k : AutKind} (hk : k ≠ .inner) :
    ¬ InducesStdKind L (1 : G) k :=
  not_inducesStdKind_of_not_inducesOuterTheta L (not_inducesOuterTheta_one L) hk

theorem not_inducesStdKind_one_field : ¬ InducesStdKind L (1 : G) .field :=
  not_inducesStdKind_one L (by decide)

theorem not_inducesStdKind_one_graphField : ¬ InducesStdKind L (1 : G) .graphField :=
  not_inducesStdKind_one L (by decide)

end Induced

end CFSG.RankThree.PartTwo.KFacts
