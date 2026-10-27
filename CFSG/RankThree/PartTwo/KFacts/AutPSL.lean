module

public import CFSG.RankThree.PartTwo.KFacts.AutKinds
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherGraphFieldInvolution
import CFSG.LocalAnalysis.ComponentInitial.ScalarSemilinearNormalizer

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix

variable (n : ℕ) (K : Type*) [Field K]

theorem slConjugation_toGL (g h : SpecialLinearGroup (Fin n) K) :
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n K
      (SpecialLinearGroup.toGL g) h = g * h * g⁻¹ := by
  apply SpecialLinearGroup.toGL_injective
  rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation, map_mul,
    map_mul, map_inv]

theorem conj_proj_eq_conjAut (g : SpecialLinearGroup (Fin n) K) :
    MulAut.conj (proj n K g) = conjAut n K (SpecialLinearGroup.toGL g) := by
  ext x
  obtain ⟨h, rfl⟩ := proj_surjective n K x
  rw [MulAut.conj_apply, conjAut_proj, ← map_mul, ← map_inv, ← map_mul, slConjugation_toGL]

theorem innAut_le_linearAutGroup :
    (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range ≤ linearAutGroup n K := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨g, rfl⟩ := proj_surjective n K x
  rw [conj_proj_eq_conjAut]
  exact conjAut_mem_linearAutGroup _

@[expose] noncomputable def stdPinnedPSL : PinnedAut (projectiveSL n K) where
  inndiag := linearAutGroup n K
  inn_le := innAut_le_linearAutGroup n K
  field := (fieldAut n K).range
  graph := {dualAut n K}

theorem stdPinnedPSL_inndiag : (stdPinnedPSL n K).inndiag = linearAutGroup n K :=
  rfl

theorem stdPinnedPSL_field : (stdPinnedPSL n K).field = (fieldAut n K).range :=
  rfl

theorem stdPinnedPSL_graph : (stdPinnedPSL n K).graph = {dualAut n K} :=
  rfl

@[expose] noncomputable def standardFieldGraph : Subgroup (MulAut (projectiveSL n K)) :=
  Subgroup.closure (Set.range (fieldAut n K) ∪ {dualAut n K})

variable {n K}

theorem fieldAut_mem_standardFieldGraph (σ : K ≃+* K) :
    fieldAut n K σ ∈ standardFieldGraph n K :=
  Subgroup.subset_closure (Or.inl ⟨σ, rfl⟩)

theorem dualAut_mem_standardFieldGraph : dualAut n K ∈ standardFieldGraph n K :=
  Subgroup.subset_closure (Or.inr rfl)

theorem standardFieldGraph_commute [Finite K] {x y : MulAut (projectiveSL n K)}
    (hx : x ∈ standardFieldGraph n K) (hy : y ∈ standardFieldGraph n K) : Commute x y := by
  have hgen : (Set.range (fieldAut n K) ∪ {dualAut n K}).Pairwise Commute := by
    rintro a (⟨σ, rfl⟩ | rfl) b (⟨τ, rfl⟩ | rfl) -
    · change fieldAut n K σ * fieldAut n K τ = fieldAut n K τ * fieldAut n K σ
      rw [← map_mul, ← map_mul, CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm K σ τ]
    · exact (dualAut_mul_fieldAut σ).symm
    · exact dualAut_mul_fieldAut τ
    · exact Commute.refl _
  have hcomm := Subgroup.isMulCommutative_closure hgen
  exact congrArg Subtype.val (hcomm.is_comm.comm (⟨x, hx⟩ : standardFieldGraph n K) ⟨y, hy⟩)

theorem standardFieldGraph_le_normalizer :
    standardFieldGraph n K ≤ Subgroup.normalizer (linearAutGroup n K : Set _) := by
  obtain ⟨-, -, hfc, hδδ, hδc, -, -⟩ := standard_automorphism_transport (K := K) (n := n)
  have hδinv : (dualAut n K)⁻¹ = dualAut n K := inv_eq_of_mul_eq_one_right hδδ
  have hconj : ∀ e : MulAut (projectiveSL n K),
      (∀ A, ∃ B, e * conjAut n K A * e⁻¹ = conjAut n K B) →
      (∀ A, ∃ B, e⁻¹ * conjAut n K A * e = conjAut n K B) →
      e ∈ Subgroup.normalizer (linearAutGroup n K : Set _) := by
    intro e h1 h2
    rw [Subgroup.mem_normalizer_iff]
    intro d
    rw [linearAutGroup_eq_range]
    constructor
    · rintro ⟨A, rfl⟩
      obtain ⟨B, hB⟩ := h1 A
      exact ⟨B, hB.symm⟩
    · rintro ⟨B, hB⟩
      obtain ⟨C, hC⟩ := h2 B
      refine ⟨C, ?_⟩
      rw [← hC, hB]
      group
  rw [standardFieldGraph, Subgroup.closure_le]
  rintro e (⟨σ, rfl⟩ | rfl)
  · refine hconj _ (fun A => ⟨_, hfc σ A⟩) fun A =>
    ⟨GeneralLinearGroup.map ((σ⁻¹ : K ≃+* K) : K →+* K) A, ?_⟩
    have h := hfc σ⁻¹ A
    rwa [map_inv, inv_inv] at h
  · refine hconj _ (fun A => ⟨GeneralLinearGroup.inverseTranspose A, ?_⟩)
      fun A => ⟨GeneralLinearGroup.inverseTranspose A, ?_⟩
    · rw [hδinv]
      exact hδc A
    · rw [hδinv]
      exact hδc A

theorem exists_conjAut_mul_mem_standardFieldGraph [Finite K] (hn : 3 ≤ n)
    (α : MulAut (projectiveSL n K)) :
    ∃ A : GL (Fin n) K, ∃ r ∈ standardFieldGraph n K, α = conjAut n K A * r := by
  obtain ⟨-, hform⟩ := automorphism_generation (K := K) hn
  obtain ⟨A, σ, ε, -, rfl⟩ := hform α
  exact ⟨A, fieldAut n K σ * dualAut n K ^ ε, mul_mem (fieldAut_mem_standardFieldGraph σ)
    (pow_mem dualAut_mem_standardFieldGraph ε), by rw [mul_assoc]⟩

theorem exists_conj_eq_of_mem_standardFieldGraph [Finite K] (hn : 3 ≤ n)
    (α : MulAut (projectiveSL n K)) :
    ∃ A : GL (Fin n) K, ∀ X ∈ standardFieldGraph n K,
      α * X * α⁻¹ = conjAut n K A * X * (conjAut n K A)⁻¹ := by
  obtain ⟨A, r, hr, rfl⟩ := exists_conjAut_mul_mem_standardFieldGraph hn α
  refine ⟨A, fun X hX => ?_⟩
  have h := (standardFieldGraph_commute hr hX).eq
  calc conjAut n K A * r * X * (conjAut n K A * r)⁻¹ =
      conjAut n K A * (r * X) * r⁻¹ * (conjAut n K A)⁻¹ := by group
    _ = conjAut n K A * X * (conjAut n K A)⁻¹ := by rw [h]; group

theorem stdPinnedPSL_stable [Finite K] (hn : 3 ≤ n) : (stdPinnedPSL n K).Stable where
  normal := by
    refine ⟨fun d hd α => ?_⟩
    obtain ⟨A, r, hr, rfl⟩ := exists_conjAut_mul_mem_standardFieldGraph hn α
    have hrd : r * d * r⁻¹ ∈ linearAutGroup n K :=
      (Subgroup.mem_normalizer_iff.mp (standardFieldGraph_le_normalizer hr) d).mp hd
    have h : conjAut n K A * r * d * (conjAut n K A * r)⁻¹ =
        conjAut n K A * (r * d * r⁻¹) * (conjAut n K A)⁻¹ := by group
    rw [h]
    exact mul_mem (mul_mem (conjAut_mem_linearAutGroup A) hrd)
      (inv_mem (conjAut_mem_linearAutGroup A))
  field_conj := by
    rintro α _ ⟨σ, rfl⟩ h1
    obtain ⟨A, hA⟩ := exists_conj_eq_of_mem_standardFieldGraph hn α
    exact ⟨fieldAut n K σ, ⟨σ, rfl⟩, h1, conjAut n K A, conjAut_mem_linearAutGroup A,
      hA _ (fieldAut_mem_standardFieldGraph σ)⟩
  graph_conj := by
    rintro α γ hγ h1
    rw [stdPinnedPSL_graph, Set.mem_singleton_iff] at hγ
    subst hγ
    obtain ⟨A, hA⟩ := exists_conj_eq_of_mem_standardFieldGraph hn α
    exact ⟨dualAut n K, rfl, h1, conjAut n K A, conjAut_mem_linearAutGroup A,
      hA _ dualAut_mem_standardFieldGraph⟩
  graphField_conj := by
    rintro α γ _ hγ hγ1 ⟨σ, rfl⟩ hφ1
    rw [stdPinnedPSL_graph, Set.mem_singleton_iff] at hγ
    subst hγ
    obtain ⟨A, hA⟩ := exists_conj_eq_of_mem_standardFieldGraph hn α
    exact ⟨dualAut n K, rfl, hγ1, fieldAut n K σ, ⟨σ, rfl⟩, hφ1, conjAut n K A,
      conjAut_mem_linearAutGroup A,
      hA _ (mul_mem dualAut_mem_standardFieldGraph (fieldAut_mem_standardFieldGraph σ))⟩

section Induced

variable {G : Type*} [Group G] [Finite G] (L : Subgroup G)

variable (n K) in
@[expose] def InducesKindPSL (x : G) (k : AutKind) : Prop :=
  ∃ e : L ⧸ aschbacherSolvableCore 3 L ≃* projectiveSL n K,
    InducesKind L (stdPinnedPSL n K) e x k

variable (n K) in
@[expose] def InducesKindSL (x : G) (k : AutKind) : Prop :=
  ∃ e : L ⧸ aschbacherSolvableCore 3 L ≃* SpecialLinearGroup (Fin n) K,
    ∃ hx : x ∈ Subgroup.normalizer (L : Set G),
      (stdPinnedPSL n K).HasKind (descendAut n K (inducedAutHom L e ⟨x, hx⟩)) k

theorem inducesKindPSL_iff [Finite K] (hn : 3 ≤ n)
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* projectiveSL n K) (x : G) (k : AutKind) :
    InducesKindPSL n K L x k ↔ InducesKind L (stdPinnedPSL n K) e x k := by
  constructor
  · rintro ⟨e', h⟩
    exact (inducesKind_iff_of_stable L (stdPinnedPSL_stable hn) e' e x k).1 h
  · intro h
    exact ⟨e, h⟩

theorem inducesKindSL_iff [Finite K] (hn : 3 ≤ n)
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* SpecialLinearGroup (Fin n) K) (x : G) (k : AutKind) :
    InducesKindSL n K L x k ↔
      ∃ hx : x ∈ Subgroup.normalizer (L : Set G),
        (stdPinnedPSL n K).HasKind (descendAut n K (inducedAutHom L e ⟨x, hx⟩)) k := by
  constructor
  · rintro ⟨e', hx, h⟩
    refine ⟨hx, ?_⟩
    rw [inducedAutHom_eq_conj L e' e, map_mul, map_mul, map_inv]
    exact ((stdPinnedPSL_stable hn).hasKind_conj _ _ k).2 h
  · rintro ⟨hx, h⟩
    exact ⟨e, hx, h⟩

end Induced

end CFSG.RankThree.PartTwo.KFacts
