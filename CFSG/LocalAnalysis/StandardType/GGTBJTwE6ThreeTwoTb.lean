module

public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6ThreeGlue
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc
  TableBExc.E6Three CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTwE6Three_tbGroup_of_label_one
     
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {Bs X : Subgroup G}
    (hBs : IsElemAbelian 3 Bs)
    (hSC : ∀ a ∈ Subgroup.centralizer (Bs : Set G), a ^ 3 = 1 → a ∈ Bs)
    (hInn : GGInnerDiagOn Bs X) (hXc : commutator ↥X = ⊤)
    (hΛ : LargeEvenInLambda2 (⟨.twE6, 0, 1⟩ : LargeEvenLabel))
    (hXl : GGHasLabel (⟨.twE6, 0, 1⟩ : LargeEvenLabel) (↥X ⧸ Subgroup.center ↥X))
    (hrk : ∀ hN : Bs ≤ Subgroup.normalizer (X : Set G),
      3 ^ 5 ≤ Nat.card (ggGamma X hN).range) :
    ∃ (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (K : Type) (_ : Field K) (_ : Finite K)
      (_ : Nat.card K = (2 ^ 1) ^ 2) (ψ₀ : ↥X →* TwE6Delta.RecipeR K 1),
      GGTorusTBGroup 3 5 (TwE6Delta.RecipeR K 1) (TwE6Delta.RecipeI K 1) ↥X ψ₀
        (ggGamma X hN).range :=
  ggTwE6Three_tbGroup_of_label hRig hBs hSC hInn hXc hΛ hXl hrk

theorem ggTwE6Three_hKer_one
    {G : Type} [Group G] [Finite G] {Bs X : Subgroup G} (hBs : IsElemAbelian 3 Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2)
    {ψ₀ : ↥X →* TwE6Delta.RecipeR K 1}
    (hTB : GGTorusTBGroup 3 5 (TwE6Delta.RecipeR K 1) (TwE6Delta.RecipeI K 1) ↥X ψ₀
      (ggGamma X hN).range) :
    ∀ g : ↥(X ⊓ Subgroup.normalizer (Bs : Set G)), ggTDρA hN g = 1 → ggTDρB X Bs g = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨w, hw⟩ :=
    TwE6ThreeLang.ggTorusTorW_recipe_twE6_three (n := 1) le_rfl hK (by norm_num)
      ↥X ψ₀ (ggGamma X hN).range hTB
  intro g hg
  exact ggTD_ker hN hw (by norm_num) hBs g hg

end CFSG.StandardType

end
