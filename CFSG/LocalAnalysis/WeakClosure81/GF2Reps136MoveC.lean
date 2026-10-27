module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136MoveA
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136MoveSimple
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W]

theorem move_trans (hw2 : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)} {t : MulAut W}
    {L : Subgroup (MulAut W)} {I : Subgroup W} (S : Move136 Y t L I) (hT : Tcl Y L) :
    ∀ I₁ ∈ irrSet L, ∀ I₂ ∈ irrSet L, ∃ g ∈ Y ⊓ Subgroup.normalizer (L : Set (MulAut W)),
      I₂ = I₁.map g.toMonoidHom := by
  exact w1369_move_trans_aux hw2 S hT

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
