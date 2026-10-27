module

public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6LeviSplit
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6LeviSplitThreeCell
public import CFSG.LocalAnalysis.StandardType.GGTBJETypeCells
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6EnnModel
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTBJTwE6LeviK_foldThree
    (hRig : GGLabelRigidInput) :
    GGTBJETypeLeviK .twE6 fun p n labJ => ggTBJTwE6RowCand p n labJ ∨
      ¬ (p = 3 ∧ 3 ∣ 2 ^ n - 1) := by
  intro G _ _ p B Bs x L D J y K hH hJK _ _ _ n hΛ hK _ _ _ _ _ hnc
  have hP : p = 3 ∧ 3 ∣ 2 ^ n - 1 := by
    by_contra h
    exact hnc (Or.inr h)
  obtain ⟨hp3, h3⟩ := hP
  subst hp3
  exact ggTBJTwE6LeviK_minus_three hRig hH hJK hΛ hK h3

end CFSG.StandardType

end
