module

public import CFSG.CGT.Timmesfeld75.Defs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Timmesfeld.RootSubgroupBasic

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open Matrix CFSG.Assembly.LowTwoRank

@[expose] def Tim75aTINotWCRoot : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (D : Set Y), CFSG.Timmesfeld.Hyp Y D →
    ∀ A : Subgroup Y, A ≠ ⊥ → (∀ a ∈ A, a ≠ 1 → a ∈ D) → Assembly.IsElemAbelian 2 A →
      IsTI A → ¬ IsWC A → ∃ d ∈ D, A ≤ CFSG.Timmesfeld.rootGroup D d

end CFSG.RankThree.GF2n.Tim79a
