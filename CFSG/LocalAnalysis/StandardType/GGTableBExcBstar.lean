module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcRank

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

namespace TableBExc

variable {τ : Tag} {K : Type} [Field K]

theorem ggBstarBound_of_input [Finite K] [CharP K 2] (hτ : τ = .E7 ∨ τ = .E8) {f : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime) (hpq : p ∣ Nat.card K - 1)
    (hT : GGExcToralRankInput τ K p) (I : Set (MulAut (RecipeGroup τ K))) :
    GGBstarBound p τ.rank (RecipeGroup τ K) I := by
  intro Eb Eh _ _ hr _ _ hEh hcard
  exfalso
  have := finite_recipeGroup τ K
  have hZ := center_recipeGroup_eq_bot τ K
  have h1 := TableBSymp.card_le_of_isCyclic_outer hp.pos (isCyclic_outer_recipe_E7_E8 hτ hf hK)
    hEh
  obtain ⟨A', hA', hA'c⟩ := TableBSymp.exists_of_subset_inn hZ
    (fun φ hφ => (inf_le_right : Eh ⊓ inner (RecipeGroup τ K) ≤ inner (RecipeGroup τ K)) hφ)
    (TableB.isElemAbelian_mono hEh inf_le_left)
  have hV : Nat.card (torusPow τ K p) = p ^ τ.rank := by
    rcases hτ with rfl | rfl
    · exact card_torusPow_E7 hp hpq
    · exact card_torusPow_E8 hp hpq
  have h2 : Nat.card A' ≤ p ^ τ.rank := by
    have h3 := hT.card_le hV (E := A'.map (recipeEquiv τ K).toMonoidHom)
      (TableB.isElemAbelian_map hA' _)
    rwa [Subgroup.card_map_of_injective (recipeEquiv τ K).injective] at h3
  have h4 : p ^ (τ.rank + 2) ≤ p ^ (τ.rank + 1) := by
    calc p ^ (τ.rank + 2) = p ^ 2 * p ^ τ.rank := by ring
      _ ≤ p ^ 2 * Nat.card Eb := Nat.mul_le_mul_left _ hr
      _ ≤ Nat.card Eh := hcard
      _ ≤ p * Nat.card (Eh ⊓ inner (RecipeGroup τ K) : Subgroup (MulAut (RecipeGroup τ K))) := h1
      _ = p * Nat.card A' := by rw [hA'c]
      _ ≤ p * p ^ τ.rank := Nat.mul_le_mul_left _ h2
      _ = p ^ (τ.rank + 1) := by ring
  have := (Nat.pow_le_pow_iff_right hp.one_lt).mp h4
  omega

theorem ggBstarBound_E8_of_eleven_le [Finite K] [CharP K 2] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) (hpq : p ∣ Nat.card K - 1)
    (I : Set (MulAut (RecipeGroup .E8 K))) : GGBstarBound p 8 (RecipeGroup .E8 K) I :=
  ggBstarBound_of_input (Or.inr rfl) hf hK hp hpq
    (ggExcToralRankInput_E8_of_eleven_le hp hp11 hpq) I

theorem ggBstarBound_E7_of_eleven_le [Finite K] [CharP K 2] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) (hpq : p ∣ Nat.card K - 1)
    (I : Set (MulAut (RecipeGroup .E7 K))) : GGBstarBound p 7 (RecipeGroup .E7 K) I :=
  ggBstarBound_of_input (Or.inl rfl) hf hK hp hpq
    (ggExcToralRankInput_E7_of_eleven_le hp hp11 hpq) I

end TableBExc

end CFSG.StandardType
