module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelHolds
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelEFrame
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelCentE
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelLiftE
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelModuleME
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelShapeE
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelNormE
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelAutE
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelRecipeID
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelE6Kernel
public import CFSG.Sporadic.Th.Simple
public import CFSG.Sporadic.ThSchreier.AutCore

public section

namespace CFSG.StandardType.E6ThreeModel

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc.E6Three
  CFSG.RankThree.CentralCover CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {K : Type} [Field K] [Finite K]

theorem eFrame_good [CharP K 2] {ζ : Kˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) :
    (eFrame K ζ hζ).Good where
  center := eFrame_center
  faithful := eFrame_faithful hζo hζ
  shape := eFrame_shape hζo hζ
  torus := eFrame_torus hζ
  cent := eFrame_cent hζo hζ
  inner := eFrame_inner hζo hζ
  weyl := eFrame_weyl hζo hζ
  modules := eFrame_modules hζo hζ
  norm := eFrame_norm hζ
  aut := eFrame_aut hζo hζ

theorem coverOdd_E (n : ℕ) (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) :
    CoverOdd (adjointGroup .E6 K) := by
  refine coverOdd_transport (TableBExc.recipeEquiv .E6 K) ?_
  intro L' _ _ ψ hψ hker hperf
  exact ⟨0, by simpa using TableBExc.E6Three.card_ker_dvd_three_e6 hn hK hψ hker hperf⟩

theorem e6ThreeModel_holds_E (hAL : GGAbelianLift) (n : ℕ) (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    (h3 : 3 ∣ 2 ^ n - 1) :
    GGE6ThreeModelSCr (TableBExc.RecipeGroup .E6 K) (TableBExc.RecipeID .E6 K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hK])
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζ, hζo⟩ : ∃ ζ : Kˣ, orderOf ζ = 3 :=
    exists_prime_orderOf_dvd_card' 3 (by rw [Nat.card_units, hK]; exact h3)
  have hζ : ζ ^ 3 = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
  refine modelSCr_transport (TableBExc.recipeEquiv .E6 K).symm (eFrame K ζ hζ).H
    (TableBExc.RecipeID .E6 K) ?_ (modelSCr_of_good hAL _ (eFrame_good hζo hζ)
      (coverOdd_E n hn hK) _ rfl)
  intro φ
  refine (recipeID_iff_hatAut φ).trans ?_
  have h : (MulAut.congr (TableBExc.recipeEquiv .E6 K).symm).symm φ =
      MulAut.congr (TableBExc.recipeEquiv .E6 K) φ := by
    ext x
    simp
  rw [h]
  exact Iff.rfl

end CFSG.StandardType.E6ThreeModel
