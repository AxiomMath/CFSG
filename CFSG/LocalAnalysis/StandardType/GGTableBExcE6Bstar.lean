module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Aut

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace TableBExc

variable {K : Type} [Field K]

theorem ggBstarBound_E6_of_input [Finite K] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hpq : p ∣ Nat.card K - 1)
    (hT : GGExcToralRankInput .E6 K p) (I : Set (MulAut (RecipeGroup .E6 K))) :
    GGBstarBound p 6 (RecipeGroup .E6 K) I := by
  intro Eb Eh _ _ hr _ _ hEh hcard
  exfalso
  have := finite_recipeGroup .E6 K
  have hZ := center_recipeGroup_eq_bot .E6 K
  set N := (MulAut.conj : RecipeGroup .E6 K →* MulAut (RecipeGroup .E6 K)).range with hN
  have h1 := card_le_mul_card_inf_inn_recipe_E6 hf hK hp hp2 hp3 hEh
  obtain ⟨A', hA', hA'c⟩ := TableBSymp.exists_of_subset_inn hZ
    (fun φ hφ => (inf_le_right : Eh ⊓ N ≤ N) hφ) (TableB.isElemAbelian_mono hEh inf_le_left)
  have hV : Nat.card (torusPow .E6 K p) = p ^ Tag.E6.rank := card_torusPow_E6 hp hp3 hpq
  have h2 : Nat.card A' ≤ p ^ 6 := by
    have h3 := hT.card_le hV (E := A'.map (recipeEquiv .E6 K).toMonoidHom)
      (TableB.isElemAbelian_map hA' _)
    rwa [Subgroup.card_map_of_injective (recipeEquiv .E6 K).injective] at h3
  have h4 : p ^ (6 + 2) ≤ p ^ (6 + 1) := by
    calc p ^ (6 + 2) = p ^ 2 * p ^ 6 := by ring
      _ ≤ p ^ 2 * Nat.card Eb := Nat.mul_le_mul_left _ hr
      _ ≤ Nat.card Eh := hcard
      _ ≤ p * Nat.card (Eh ⊓ N : Subgroup (MulAut (RecipeGroup .E6 K))) := h1
      _ = p * Nat.card A' := by rw [hA'c]
      _ ≤ p * p ^ 6 := Nat.mul_le_mul_left _ h2
      _ = p ^ (6 + 1) := by ring
  have := (Nat.pow_le_pow_iff_right hp.one_lt).mp h4
  omega

end TableBExc

end CFSG.StandardType
