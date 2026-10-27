module

public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3F4ShapeSix
public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3F4NotRank3

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (StatedLieTag)

theorem ggLieF4Plane_shape
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {D : LangDatum Tag.F4 L}
    {ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)} {a₁ a₂ : Fin Tag.F4.rank → Lˣ}
    (h : GGLieF4PlaneHyp D ρ a₁ a₂)
    (i : KernelComponent (jointChar a₁ a₂)) :
    GGLieF4PlaneShape (componentRoots (jointChar a₁ a₂) i) := by
  exact (ggLieF4Plane_shape_six h i).resolve_right (ggLieF4Plane_not_rank_three h i)

end CFSG.StandardType.LieCore
