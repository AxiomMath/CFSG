module

public import CFSG.RankThree.PartTwo.Sec21.Item22Statements

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

@[expose] def List228Sixteen : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y],
    (Nonempty (Y ≃* SL3 2) ∨ Nonempty (Y ≃* projSp 2 (GaloisField 2 2)) ∨
      Nonempty (Y ≃* projSU 4 2 2) ∨ Nonempty (Y ≃* projSU 5 2 2) ∨
      StatedClassicalModel Y .PSL 4 2 1 ∨ StatedClassicalModel Y .PSL 5 2 1) →
    ∃ E : Subgroup Y, IsElemAbelian 2 E ∧ Nat.card E = 2 ^ 4

end CFSG.RankThree.PartTwo.Sec21
