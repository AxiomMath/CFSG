module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Cent361

public section

namespace CFSG.RankThree.PartTwo.Sec15.GagenL3

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] def Res1L3Q (X : Type) [Group X] : Prop :=
  IsLThreePi X ∧ IsSimpleGroup X ∧
    ∃ E : Subgroup X, CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9

theorem res1QE9_of_le {Q : ∀ (X : Type) [Group X], Prop}
    (hQ : ∀ (X : Type) [Group X], Q X → Res1L3Q X) : Sylow155R1.Res1QE9 Q :=
  fun X _ h => (hQ X h).2

theorem res1QE9_l3 : Sylow155R1.Res1QE9 Res1L3Q :=
  res1QE9_of_le fun _ _ h => h

@[expose] def Res1L3QEven (X : Type) [Group X] : Prop :=
  Res1L3Q X ∧ ∃ e : ℕ, 1 ≤ e ∧ Sec4.IsoLThreePi X 2 e

end CFSG.RankThree.PartTwo.Sec15.GagenL3
