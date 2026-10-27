module

public import CFSG.LocalAnalysis.StandardType.GGTableBF4Rank
public import CFSG.LieType.Chevalley.EvenF4AutomorphismNormalForm

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

namespace TableBF4

theorem isCyclic_outer_of_hom {P C : Type*} [Group P] [Group C] [IsCyclic C]
    (Θ : MulAut P →* C) (hsurj : Function.Surjective Θ) (hker : Θ.ker = inner P) :
    IsCyclic (Outer P) := by
  let e : Outer P ≃* C :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective Θ hsurj)
  exact (MulEquiv.isCyclic e).2 inferInstance

variable {K : Type} [Field K]

theorem isCyclic_outer_adjointF4 [Finite K] [CharP K 2] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) : IsCyclic (Outer (adjointGroup .F4 K)) := by
  have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := ‹CharP K 2›
  obtain ⟨-, -, ⟨Θ, -, hsurj, hker⟩, -⟩ := even_F4_exact_automorphism_normal_form hf K hK
  exact isCyclic_outer_of_hom Θ hsurj hker

theorem isCyclic_outer_F4 [Finite K] [CharP K 2] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) : IsCyclic (Outer (RecipeGroup K)) := by
  have h := isCyclic_outer_adjointF4 hf hK
  let e := CFSG.ComponentClassification.OuterAutomorphisms.equivalence (recipeEquiv K)
  exact (MulEquiv.isCyclic e).2 h

theorem finite_recipeGroup [Finite K] : Finite (RecipeGroup K) := by
  have : Finite (adjointGroup .F4 K) := generated_group_finite .F4 K
  exact Finite.of_equiv _ (recipeEquiv K).symm.toEquiv

theorem ggBstarBound_F4_of_input [Finite K] [CharP K 2] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime) (hpq : p ∣ Nat.card K - 1)
    (hT : GGF4ToralRankInput K p) (I : Set (MulAut (RecipeGroup K))) :
    GGBstarBound p 4 (RecipeGroup K) I := by
  intro Eb Eh _ _ hr _ _ hEh hcard
  exfalso
  have := finite_recipeGroup (K := K)
  have hZ := center_recipeGroup_eq_bot K
  have h1 := TableBSymp.card_le_of_isCyclic_outer hp.pos (isCyclic_outer_F4 hf hK) hEh
  obtain ⟨A', hA', hA'c⟩ := TableBSymp.exists_of_subset_inn hZ
    (fun φ hφ => (inf_le_right : Eh ⊓ inner (RecipeGroup K) ≤ inner (RecipeGroup K)) hφ)
    (TableB.isElemAbelian_mono hEh inf_le_left)
  have h2 : Nat.card A' ≤ p ^ 4 := by
    have h3 := hT.card_le hp hpq (E := A'.map (recipeEquiv K).toMonoidHom)
      (TableB.isElemAbelian_map hA' _)
    rwa [Subgroup.card_map_of_injective (recipeEquiv K).injective] at h3
  have h4 : p ^ 6 ≤ p ^ 5 := by
    calc p ^ 6 = p ^ 2 * p ^ 4 := by ring
      _ ≤ p ^ 2 * Nat.card Eb := Nat.mul_le_mul_left _ hr
      _ ≤ Nat.card Eh := hcard
      _ ≤ p * Nat.card (Eh ⊓ inner (RecipeGroup K) : Subgroup (MulAut (RecipeGroup K))) := h1
      _ = p * Nat.card A' := by rw [hA'c]
      _ ≤ p * p ^ 4 := Nat.mul_le_mul_left _ h2
      _ = p ^ 5 := by ring
  have := (Nat.pow_le_pow_iff_right hp.one_lt).mp h4
  omega

theorem ggBstarBound_F4 [Finite K] [CharP K 2] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K - 1)
    (I : Set (MulAut (RecipeGroup K))) : GGBstarBound p 4 (RecipeGroup K) I :=
  ggBstarBound_F4_of_input hf hK hp hpq (ggF4ToralRankInput_of_five_le hp hp5 hpq) I

end TableBF4

end CFSG.StandardType
