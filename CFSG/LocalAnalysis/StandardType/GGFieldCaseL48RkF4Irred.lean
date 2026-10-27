module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBBridge
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBRkDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBE6TwoTBSec
public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoTBTorus
public import CFSG.LocalAnalysis.StandardType.GGF4TwoNTFrame
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBE7E8

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CorFourTwoMore

private theorem ggTorusIrredSecElt_adjoint_F4_two
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) : GGTorusIrredSecElt 3 4 (adjointGroup .F4 K) := by
  intro E hE h4 _
  obtain ⟨c, hc⟩ := F4TwoNonToral.exists_conj_frame_of_card_F4 K hK E hE h4
  rw [hc]
  exact TableBExcTwoTB.secEltAt_map_conj (TableBF4TwoTB.secEltAt_F4 hK) c

private theorem ggTorusIrred_F4_two
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) :
    GGTorusIrred 3 4 (TableBF4.RecipeGroup K) (TableBF4.RecipeID K) :=
  ggTorusIrred_of_irredSecElt Nat.prime_three (TableBF4.idImage_subset_inn K)
    (TableBF4.center_recipeGroup_eq_bot K)
    (ggTorusIrredSecElt_of_mulEquiv (TableBF4.recipeEquiv K)
      (ggTorusIrredSecElt_adjoint_F4_two hK))

theorem ggL48IrredModRkF4Two_holds :
    ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
      LargeEvenSplit p lab → ¬ GGL48TableBVacLabel p lab → GGL48F4TwoThreeLabel p lab →
        LargeEvenLabelAll lab fun R _ I _ => GGIrredModTableBRk p R I 5 := by
  intro p lab hp hlab hsplit hnotvac hF
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hn, rfl⟩ := hF
  dsimp only at htag hn
  subst htag
  subst hn
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have hK2 : Nat.card K = 2 := by simpa only [pow_one] using hK
  have : CharP K 2 := charP_two_of_card hK
  exact ⟨K, inferInstance, inferInstance, hK, hQ',
    ggIrredModTableBRk_of_torusIrred Nat.prime_three (ggTorusIrred_F4_two hK2)⟩

end CFSG.StandardType

end
