module

public import CFSG.LocalAnalysis.StandardType.GGRealKGThree
public import CFSG.LocalAnalysis.StandardType.GGRealKGExcNegC
public import CFSG.LocalAnalysis.StandardType.GGF4ThreeNoReflection
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLine
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusLift

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem ggKGRootDatum_F4_nonsplit_three
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (hpq : 3 ∣ Nat.card K + 1) (hq : 4 ≤ Nat.card K) :
    GGKGRootDatum 3 3 (adjointGroup .F4 K) := by
  intro E hE h3 _ hSC w hr
  obtain ⟨F, hlong⟩ := exists_excFrame_of_selfCentralizing_of_reflection_three hpq hE h3
    (fun x hx hxp => hSC x (fun e he => (Subgroup.mem_centralizer_iff.mp hx e he).symm) hxp) hr
  exact ggRealKGNeg_rootDatumAt (Or.inr (Or.inr rfl)) Nat.prime_three le_rfl hpq hq F hlong w hr

private theorem f4NonsplitThree_recipe {n : ℕ}
    (hpn : 3 ∣ 2 ^ n + 1)
    (hn : 2 ≤ n)
    {Q : LargeEvenRawCont} (h : LargeEvenRecipeChevalley Tag.F4.cartan (2 ^ n) false Q) :
    LargeEvenRecipeChevalley Tag.F4.cartan (2 ^ n) false
      (fun R _ I F => Q R I F ∧ ∃ r, GGTorusLift 3 r R ∧ GGTorusRootSL2 3 r R I) := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have : CharP K 2 := charP_two_of_card hK
  have hpq : 3 ∣ Nat.card K + 1 := by rw [hK]; exact hpn
  have hq : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hdatum : GGKGRootDatum 3 3 (TableBF4.RecipeGroup K) :=
    ggKGRootDatum_of_mulEquiv (TableBF4.recipeEquiv K) (ggKGRootDatum_F4_nonsplit_three hpq hq)
  refine ⟨K, inferInstance, inferInstance, hK, hQ, 3,
    ggTorusLift_F4Plus Nat.prime_three (by norm_num) hpq, ?_⟩
  exact ggTorusRootSL2_of_rootDatum Nat.prime_three
    (fun φ hφ _ => TableBF4.idImage_subset_inn K hφ)
    (TableBF4.center_recipeGroup_eq_bot K)
    (ExcSplitL.ggCenterPrime_recipe_F4 Nat.prime_three (by norm_num)) hdatum

theorem ggRealKGThreeRow_f4Nonsplit : GGRealKGThreeRow .f4Nonsplit := by
  intro p lab _ _ hreal hs
  obtain ⟨rfl, ⟨htag, hpn⟩, -⟩ := hs
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpn hreal
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  exact f4NonsplitThree_recipe hpn hreal.2.1 hQ

end CFSG.StandardType

end
