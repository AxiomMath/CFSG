module

public import CFSG.LocalAnalysis.StandardType.GGKGLayersE6
public import CFSG.LocalAnalysis.StandardType.GGKGLayersGlue
public import CFSG.LocalAnalysis.StandardType.GGKGMult
public import CFSG.LocalAnalysis.StandardType.GGKGRankOne
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelKGFrameE

public section

namespace CFSG.StandardType.KGL

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.KE8F CFSG.StandardType.LayerSixE
  CFSG.StandardType.TableBExc CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.NoOffRest
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


theorem kgLayers_E6_holds :
    ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = 2 ^ n → 3 ∣ 2 ^ n - 1 →
      GGE6KGLayers (RecipeGroup Tag.E6 K) (RecipeID Tag.E6 K) :=
  kgLayers_E6_of_adj kgAdjL1 kgAdjL2 kgAdjL3i kgAdjL3ii kgAdjL4 kgAdjM kgFrameE6_holds

end CFSG.StandardType.KGL

end
