module

public import CFSG.LocalAnalysis.StandardType.GGWPlusDefs
public import CFSG.LocalAnalysis.StandardType.GGWPlusPerm
public import CFSG.LocalAnalysis.StandardType.GGWPlusE6Weyl
public import CFSG.LocalAnalysis.StandardType.GGWPlusE6Auto
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelHoldsT
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelAbelianLift
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Delta

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley

theorem ggSolvQuotLeTwo_twE6_three
    {K : Type} [Field K] [Finite K] (n : ℕ) (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (h3 : 3 ∣ 2 ^ n + 1) {Eb : Subgroup (MulAut (TwE6Delta.RecipeR K n))}
    (hA : IsElemAbelian 3 Eb) (hI : (Eb : Set (MulAut (TwE6Delta.RecipeR K n))) ⊆
      TwE6Delta.RecipeI K n)
    (hr : 3 ^ 5 ≤ Nat.card Eb) (hsc : GGTorusSelfCent 3 Eb)
    (hperf : commutator (TwE6Delta.RecipeR K n) = ⊤) :
    GGSolvQuotLeTwo
      ((MulAut.conj : TwE6Delta.RecipeR K n →* MulAut (TwE6Delta.RecipeR K n)).range ⊓
        Subgroup.normalizer (Eb : Set (MulAut (TwE6Delta.RecipeR K n))))
      (Subgroup.centralizer (Eb : Set (MulAut (TwE6Delta.RecipeR K n)))) := by
  haveI : Finite (TwE6Delta.RecipeR K n) := TwE6Delta.finite_recipeR hK
  have hSCr : GGE6ThreeModelSCr (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) :=
    E6ThreeModel.e6ThreeModel_holds_T (hn := hn) (hK := hK) ggAbelianLift h3
  have hmodel : GGE6ThreeWeylModel
      (MonoidHom.id (TwE6Delta.RecipeR K n)).ker Eb :=
    hSCr (TwE6Delta.RecipeR K n) (MonoidHom.id _)
      (fun x => ⟨x, rfl⟩) (by rw [MonoidHom.ker_id]; exact bot_le) hperf Eb hA
      (fun a ha => ⟨a, hI ha, fun _ => rfl⟩) hr hsc
  obtain ⟨Φ, T, w, hdata⟩ := GGE6ThreeWeylModel.exists_data hmodel
  obtain ⟨ρ, hρs, hρk⟩ := GGE6ThreeData.exists_automizer_hom hdata
  exact ggSolvQuotLeTwo_of_surj
    (fun Q _ f hf hQ => weylE6_solvable_quotient_card_le_two f hf hQ) ρ hρs hρk

end CFSG.StandardType
