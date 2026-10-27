module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LieType.SeitzGeneration.ExcPrimeSplit
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeProofDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

open CFSG.LieType.SeitzGeneration CFSG.AGLEmbeddingD2

namespace CFSG.RankThree.PartTwo.Sec19

@[expose] def SeitzThreeLThreePiFieldTwo : Prop :=
  SeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ ¬ NarrowScope p E ∧ p = 3 ∧ IsLThreePiIndex d.1 ∧
    d.1.characteristic = 2

@[expose] def SeitzThreeSec441NoninnerTwo : Prop :=
  SeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ p = 3 ∧ IsSeitz441Index d.1 ∧
    d.1.characteristic = 2

@[expose] def SeitzThreeTrialityWideTwo : Prop :=
  SeitzPlanes fun d p E => p = 3 ∧ IsTrialityIndex d.1 ∧ d.1.characteristic = 2 ∧
    ((¬ InnerPlane d p E ∧ ¬ NarrowScope p E) ∨ (InnerPlane d p E ∧ ¬ RankLE2 p (Cat d)))

theorem seitzThreeLThreePiFieldTwo_of_wide (h : SeitzThreeLThreePiField) :
    SeitzThreeLThreePiFieldTwo :=
  SeitzPlanes.mono (fun _ _ _ hE => ⟨hE.1, hE.2.1, hE.2.2.1, hE.2.2.2.1⟩) h

end CFSG.RankThree.PartTwo.Sec19

namespace CFSG.LieType.SeitzGeneration

@[expose] def SeitzExcAnisotropicTrialityThreeTwo : Prop :=
  SeitzExcAnisotropicForAt IsTrialityIndex fun d p => p = 3 ∧ d.characteristic = 2

end CFSG.LieType.SeitzGeneration
