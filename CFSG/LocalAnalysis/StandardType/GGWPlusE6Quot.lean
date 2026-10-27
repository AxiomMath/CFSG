module

public import CFSG.LocalAnalysis.StandardType.GGWPlusDefs
public import CFSG.LocalAnalysis.StandardType.GGWPlusPerm
public import CFSG.LocalAnalysis.StandardType.GGWPlusE6Weyl
public import CFSG.LocalAnalysis.StandardType.GGWPlusE6Auto
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelHoldsE
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelAbelianLift

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley

theorem ggSolvQuotLeTwo_E6_three
    {K : Type} [Field K] [Finite K] (n : ℕ) (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    (h3 : 3 ∣ 2 ^ n - 1) {Eb : Subgroup (MulAut (TableBExc.RecipeGroup .E6 K))}
    (hA : IsElemAbelian 3 Eb) (hI : (Eb : Set (MulAut (TableBExc.RecipeGroup .E6 K))) ⊆
      TableBExc.RecipeID .E6 K)
    (hr : 3 ^ 5 ≤ Nat.card Eb) (hsc : GGTorusSelfCent 3 Eb)
    (hperf : commutator (TableBExc.RecipeGroup .E6 K) = ⊤) :
    GGSolvQuotLeTwo
      ((MulAut.conj : TableBExc.RecipeGroup .E6 K →* MulAut (TableBExc.RecipeGroup .E6 K)).range ⊓
        Subgroup.normalizer (Eb : Set (MulAut (TableBExc.RecipeGroup .E6 K))))
      (Subgroup.centralizer (Eb : Set (MulAut (TableBExc.RecipeGroup .E6 K)))) := by
  haveI : Finite (TableBExc.RecipeGroup .E6 K) := TableBExc.finite_recipeGroup .E6 K
  have hSCr : GGE6ThreeModelSCr (TableBExc.RecipeGroup .E6 K) (TableBExc.RecipeID .E6 K) :=
    E6ThreeModel.e6ThreeModel_holds_E (K := K) ggAbelianLift n hn hK h3
  have hmodel : GGE6ThreeWeylModel
      (MonoidHom.id (TableBExc.RecipeGroup .E6 K)).ker Eb :=
    hSCr (TableBExc.RecipeGroup .E6 K) (MonoidHom.id _)
      (fun x => ⟨x, rfl⟩) (by rw [MonoidHom.ker_id]; exact bot_le) hperf Eb hA
      (fun a ha => ⟨a, hI ha, fun _ => rfl⟩) hr hsc
  obtain ⟨Φ, T, w, hdata⟩ := GGE6ThreeWeylModel.exists_data hmodel
  obtain ⟨ρ, hρs, hρk⟩ := GGE6ThreeData.exists_automizer_hom hdata
  exact ggSolvQuotLeTwo_of_surj
    (fun Q _ f hf hQ => weylE6_solvable_quotient_card_le_two f hf hQ) ρ hρs hρk

end CFSG.StandardType
