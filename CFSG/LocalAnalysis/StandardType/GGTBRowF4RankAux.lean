module

public import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndModel
public import CFSG.LocalAnalysis.StandardType.GGTBRowDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwenty
public import CFSG.LocalAnalysis.StandardType.GGTableBF4
public import CFSG.LocalAnalysis.StandardType.GGTableBF4Three

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggF4Row_card_le_of_recipe
    {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hpq : p ∣ Nat.card K - 1)
    (hT : GGF4ToralRankInput K p) :
    ∀ X : Subgroup (MulAut (TableBF4.RecipeGroup K)),
      (X : Set (MulAut (TableBF4.RecipeGroup K))) ⊆ TableBF4.RecipeID K →
        IsElemAbelian p X → Nat.card X ≤ p ^ 4 := by
  intro X hXI hX
  haveI := TableBF4.finite_recipeGroup (K := K)
  obtain ⟨A', hA', hA'c⟩ := TableBSymp.exists_of_subset_inn (R := TableBF4.RecipeGroup K)
    (TableBF4.center_recipeGroup_eq_bot K)
    (fun φ hφ => TableBF4.idImage_subset_inn K (hXI hφ)) hX
  have h3 := hT.card_le hp hpq (E := A'.map (TableBF4.recipeEquiv K).toMonoidHom)
    (TableB.isElemAbelian_map hA' _)
  rw [Subgroup.card_map_of_injective (TableBF4.recipeEquiv K).injective] at h3
  rw [← hA'c]
  exact h3

theorem ggF4Row_labelAll_card
    {lab : LargeEvenLabel} (htag : lab.tag = .F4) (hlab : LargeEvenInLambda2 lab)
    {p : ℕ} (hp : p.Prime) (hpn : p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ =>
      ∀ X : Subgroup (MulAut R), (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X →
        Nat.card X ≤ p ^ 4) := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag
  subst htag
  intro Q hQ
  obtain ⟨K, _, _, hK, hQK⟩ := hQ
  haveI : CharP K 2 := charP_two_of_card hK
  have hp2 := ne_two_of_dvd_two_pow_sub_one hlab.1 hpn
  have hpq : p ∣ Nat.card K - 1 := by
    rw [hK]
    exact hpn
  have hT := ggF4ToralRankInput_of_three hp hp2 hpq fun _ => ggF4ThreeRankInput_holds
  refine ⟨K, inferInstance, inferInstance, hK, hQK, ?_⟩
  intro _ _ X hXI hX
  exact ggF4Row_card_le_of_recipe hp hpq hT X hXI hX

end CFSG.StandardType

end
