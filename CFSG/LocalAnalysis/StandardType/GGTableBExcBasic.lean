module

public import CFSG.LocalAnalysis.StandardType.GGTableBF4Bstar
public import CFSG.LieType.Chevalley.EvenE7E8AutomorphismNormalForm
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

namespace TableBExc

variable (τ : Tag) (K : Type) [Field K]

abbrev RecipeGroup : Type :=
  LargeEvenCenterQuot (LargeEvenChevH τ.cartan K false)

abbrev RecipeID : Set (MulAut (RecipeGroup τ K)) :=
  LargeEvenChevIDImage τ.cartan K (LargeEvenChevH τ.cartan K false)


@[expose] noncomputable def recipeEquiv [Finite K] : RecipeGroup τ K ≃* adjointGroup τ K :=
  (Classical.choice (centerQuot_chevGroup_equiv K τ)).trans
    ((QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := τ) (K := K))).trans
      QuotientGroup.quotientBot)

theorem center_recipeGroup_eq_bot [Finite K] : Subgroup.center (RecipeGroup τ K) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hx' : recipeEquiv τ K x ∈ Subgroup.center (adjointGroup τ K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := (recipeEquiv τ K).surjective g
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hx) y]
  rw [CFSG.LieType.Chevalley.center_adjointGroup_eq_bot, Subgroup.mem_bot] at hx'
  rw [Subgroup.mem_bot, ← (recipeEquiv τ K).map_eq_one_iff]
  exact hx'

theorem finite_recipeGroup [Finite K] : Finite (RecipeGroup τ K) := by
  have : Finite (adjointGroup τ K) := CFSG.LieType.Chevalley.generated_group_finite τ K
  exact Finite.of_equiv _ (recipeEquiv τ K).symm.toEquiv

theorem idImage_subset_inn_of_top (hT : TableB.torusSubgroup τ.cartan K = ⊤) :
    RecipeID τ K ⊆ Set.range (MulAut.conj : RecipeGroup τ K →* MulAut (RecipeGroup τ K)) := by
  have hdiag : LargeEvenChevDiagImage τ.cartan K (LargeEvenChevH τ.cartan K false) ⊆
      (MulAut.conj : RecipeGroup τ K →* MulAut (RecipeGroup τ K)).range := by
    intro φ hφ
    obtain ⟨a, ha⟩ := TableB.exists_isDiagOf hφ
    have hmem : TableB.diagHom τ.cartan K a ∈ LargeEvenChevH τ.cartan K false :=
      TableB.diagHom_mem_of_mem_torusSubgroup τ K (hT ▸ Subgroup.mem_top a)
    rw [TableB.isDiagOf_eq_conj ha hmem]
    exact ⟨_, rfl⟩
  have hle : Subgroup.closure (LargeEvenInnSet (RecipeGroup τ K) ∪
      LargeEvenChevDiagImage τ.cartan K (LargeEvenChevH τ.cartan K false)) ≤
      (MulAut.conj : RecipeGroup τ K →* MulAut (RecipeGroup τ K)).range := by
    rw [Subgroup.closure_le]
    refine Set.union_subset ?_ hdiag
    rintro _ ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  intro φ hφ
  exact hle hφ

theorem idImage_subset_inn_E8 :
    RecipeID .E8 K ⊆ Set.range (MulAut.conj : RecipeGroup .E8 K →* MulAut (RecipeGroup .E8 K)) :=
  idImage_subset_inn_of_top .E8 K
    (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K TableB.cartanE8_inv fun s => ⟨s, pow_one s⟩)

theorem idImage_subset_inn_E7 [Finite K] [CharP K 2] :
    RecipeID .E7 K ⊆ Set.range (MulAut.conj : RecipeGroup .E7 K →* MulAut (RecipeGroup .E7 K)) :=
  idImage_subset_inn_of_top .E7 K
    (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K TableB.cartanE7_adj
      (TableB.exists_sq_eq_of_charTwo K))

theorem isCyclic_ringAut {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) : IsCyclic (K ≃+* K) := by
  obtain ⟨F, -, -, hF, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hf hK
  exact isCyclic_iff_exists_zpowers_eq_top.2 ⟨F, hF⟩

variable {τ K}

theorem isCyclic_outer_adjoint_E7_E8 (hτ : τ = .E7 ∨ τ = .E8) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) : IsCyclic (Outer (adjointGroup τ K)) := by
  obtain ⟨-, Θ, -, hsurj, hker, -⟩ :=
    CFSG.LieType.Chevalley.even_E7_E8_exact_inner_field_automorphism_normal_form hf K hK τ hτ
  have := isCyclic_ringAut K hf hK
  exact TableBF4.isCyclic_outer_of_hom Θ hsurj hker

theorem isCyclic_outer_recipe_E7_E8 [Finite K] (hτ : τ = .E7 ∨ τ = .E8) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) : IsCyclic (Outer (RecipeGroup τ K)) := by
  have h := isCyclic_outer_adjoint_E7_E8 hτ hf hK
  let e := CFSG.ComponentClassification.OuterAutomorphisms.equivalence (recipeEquiv τ K)
  exact (MulEquiv.isCyclic e).2 h

end TableBExc

end CFSG.StandardType
