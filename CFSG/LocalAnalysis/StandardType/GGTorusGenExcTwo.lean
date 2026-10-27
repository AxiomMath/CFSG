module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenRTransfer
public import CFSG.LocalAnalysis.StandardType.GGTorusGenExcTwoFrame
public import CFSG.LocalAnalysis.StandardType.GGTorusGenSLTransfer
public import CFSG.LocalAnalysis.StandardType.GGTableBExcCoverRows
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLineE7
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLine
public import Certificates.Certificate1952

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

namespace ExcTwoGen

section Core


theorem ggTorusGenR_E7_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    GGTorusGenR 3 6 (TableBExc.RecipeGroup .E7 K) :=
  ggTorusGenR_of_mulEquiv (TableBExc.recipeEquiv .E7 K) (ggTorusGenR_adjoint_two (Or.inl rfl) hK)

theorem ggTorusGenR_E8_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    GGTorusGenR 3 7 (TableBExc.RecipeGroup .E8 K) :=
  ggTorusGenR_of_mulEquiv (TableBExc.recipeEquiv .E8 K) (ggTorusGenR_adjoint_two (Or.inr rfl) hK)

end Core

end ExcTwoGen

section Label


theorem ggTorusGenTableB_E7_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    GGTorusGenTableB 3 (TableBExc.RecipeGroup .E7 K) (TableBExc.RecipeID .E7 K) := by
  have : CharP K 2 := charP_two_of_card (m := 1) (by rw [hK]; norm_num)
  have hRk := ggTorusGenTableBRk_of_torusGenR (r := 6) Nat.prime_three
    (fun φ hφ _ => TableBExc.idImage_subset_inn_E7 K hφ)
    (TableBExc.center_recipeGroup_eq_bot .E7 K)
    (ExcSplitL.ggCenterPrime_recipe_E7 (f := 1) le_rfl (by rw [hK]; norm_num) Nat.prime_three
      (by norm_num))
    (ExcTwoGen.ggTorusGenR_E7_two hK)
  exact ggTorusGenTableB_of_rk (r := 7) Nat.prime_three (by norm_num)
    TableBExcTwo.ggTorusLift_E7Two hRk

theorem ggTorusGenTableB_E8_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    GGTorusGenTableB 3 (TableBExc.RecipeGroup .E8 K) (TableBExc.RecipeID .E8 K) := by
  have : CharP K 2 := charP_two_of_card (m := 1) (by rw [hK]; norm_num)
  have hRk := ggTorusGenTableBRk_of_torusGenR (r := 7) Nat.prime_three
    (fun φ hφ _ => TableBExc.idImage_subset_inn_E8 K hφ)
    (TableBExc.center_recipeGroup_eq_bot .E8 K)
    (ExcSplitL.ggCenterPrime_recipe_E8 Nat.prime_three (by norm_num))
    (ExcTwoGen.ggTorusGenR_E8_two hK)
  exact ggTorusGenTableB_of_rk (r := 8) Nat.prime_three (by norm_num)
    TableBExcTwo.ggTorusLift_E8Two hRk

theorem largeEvenLabelAll_torusGenTableB_excTwo {p : ℕ} {lab : LargeEvenLabel}
    (hrow : GGL48TBExcTwoRow p lab) (hτ : lab.tag = .E7 ∨ lab.tag = .E8) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusGenTableB p R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨-, hn, rfl⟩ := hrow
  dsimp only at hτ hn
  subst hn
  intro Q hQ
  rcases hτ with rfl | rfl
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hq⟩ := hQ
    exact ⟨K, i1, i2, hK, hq, ggTorusGenTableB_E7_two (by simpa using hK)⟩
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hq⟩ := hQ
    exact ⟨K, i1, i2, hK, hq, ggTorusGenTableB_E8_two (by simpa using hK)⟩

end Label

end CFSG.StandardType
