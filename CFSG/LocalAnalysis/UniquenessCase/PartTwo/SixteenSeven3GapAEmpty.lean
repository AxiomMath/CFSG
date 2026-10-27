module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs3
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def S16GapAEmpty (D : Data G) : Prop :=
  ∀ (V L : Subgroup G) (hV : IsElemAbelian 2 V), Counterex16 D ⊥ V L hV →
    (Case168_3 D ⊥ V hV L ∨ (∃ r : ℕ, 3 ≤ r ∧ Case168_4With D ⊥ V hV L r) ∨
      Case168_8 D ⊥ V hV ∨ Case168_9 D ⊥ V hV L ∨ Case168_10 D ⊥ V hV L ∨
      Case168_11 D ⊥ V hV L) →
    calABar (mBar D.M ⊥ V hV) D.M ⊥ V hV = ∅

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
