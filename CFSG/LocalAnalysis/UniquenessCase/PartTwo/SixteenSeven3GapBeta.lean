module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs3
public import CFSG.LocalAnalysis.WeakClosure81.SixFifteen
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def S16GapBetaBound (D : Data G) : Prop :=
  ∀ (V L : Subgroup G) (hV : IsElemAbelian 2 V), Counterex16 D ⊥ V L hV →
    (∃ r : ℕ, 3 < r ∧ Case168_4With D ⊥ V hV L r) →
      ((D.k + 1 : ℕ) : ℕ∞) < betaN D.k D.M V ∧ ((D.k + 1 : ℕ) : ℕ∞) < rMV D.M V

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
