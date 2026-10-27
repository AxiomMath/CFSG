module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.H13.ModelsSymplectic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

@[expose] def ShapeIV (X : Type) [Group X] : Prop :=
  LieModel X .PSL 3 3 1 ∨ ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ LieModel X .PSp 2 p 1

end CFSG.LocalAnalysis.WeakClosure81

end
