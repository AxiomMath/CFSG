module

public import CFSG.RankThree.PartTwo.Sec13.Notation
public import CFSG.RankThree.PartTwo.Sec8.Groups
public import CFSG.RankThree.PartTwo.Sec9.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def KFact1121Lists : Prop :=
  ∀ (X : Type) [Group X], Sec9.IsList1016 X →
    ¬ ((∃ q : TauCeti.PrimePower, Sec4.IsoGTwo X q) ∨ (∃ n : ℕ, Sec8.IsoTrialityD4 X n) ∨
      Sec13.IsLThreePi X)

end CFSG.RankThree.PartTwo.Sec11
