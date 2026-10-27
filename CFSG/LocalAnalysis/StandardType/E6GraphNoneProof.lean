module

public import CFSG.LocalAnalysis.StandardType.GGOuterInvAtE6
public import CFSG.LieType.Chevalley.E6GraphFullDiagonalCoset

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Universal CFSG.Assembly.LowTwoRank
open CFSG.LieType.Chevalley.E6GraphFullCoset (IsOrdinaryDiagGraph)
open CFSG.Open (IsElemAbelian)

theorem isOrdinaryDiagGraph_conj_mul_exactNormalAut_graph {K : Type} [Field K]
    (g : adjointGroup TwistTag.E6.tag K) (a : Fin TwistTag.E6.tag.rank → Kˣ) :
    IsOrdinaryDiagGraph K (MulAut.conj g * exactNormalAut TwistTag.E6.tag K a 1 1) := by
  refine ⟨g, a, g.2, fun h => ?_⟩
  rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv, coe_exactNormalAut, AutSt.units_map_entrywiseHom_one,
    CFSG.LieType.Chevalley.E6GraphInnerCoset.exactQ_E6, pow_one]
  group

end CFSG.StandardType
