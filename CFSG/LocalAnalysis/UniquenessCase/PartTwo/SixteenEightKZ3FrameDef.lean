module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

structure S16kFrame {W : Type} [CommGroup W] (A : Subgroup (MulAut W))
    (E : Fin 3 → Subgroup (MulAut W)) : Prop where
  le : ∀ i, E i ≤ A
  cyc : ∀ i, IsCyclicOrd ↥(E i) 3
  le_core : ∀ i, E i ≤ pCoreOf 3 A
  rk_two : ∀ i, rk ↥(commSub ⊤ (E i)) = 2
  comm : ∀ i j, ∀ x ∈ E i, ∀ y ∈ E j, x * y = y * x
  cent : ∀ i j, i ≠ j → commSub (commSub ⊤ (E i)) (E j) = ⊥
  indep : sSupIndep (Set.range fun i => commSub ⊤ (E i))
  span : (⨆ i, commSub ⊤ (E i)) = ⊤
  inj : Function.Injective E
  perm : ∀ g ∈ A, ∀ i, ∃ j, (E i).map (MulAut.conj g).toMonoidHom = E j
  trans : ∀ i j, ∃ g ∈ A, (E i).map (MulAut.conj g).toMonoidHom = E j
  noninvol : ∀ t ∈ A, t ^ 2 = 1 → t ≠ 1 → ∃ i, ⁅E i, Subgroup.zpowers t⁆ ≠ ⊥

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
