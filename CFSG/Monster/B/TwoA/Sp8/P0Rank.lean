
module


public import Certificates.Certificate812462
public import CFSG.Monster.B.TwoA.Sp8.P0RankWalk

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8.WordRel

open CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.TwoA
  CFSG.ComponentClassification.RankTwoSporadic.B.TwoDFix CFSG.Open
open MonsterB.P0Rank CFSG.Monster.B.TwoA.Sp8.P0Rank
open CFSG.KC.BvecLoop
open scoped commutatorElement
attribute [local instance low] Classical.propDecidable

theorem card_le_of_le_P0 :
    ∀ E : Subgroup Dfull, E ≤ PLam lam0 → IsElemAbelian 2 E → Nat.card E ≤ 2 ^ 14 :=
  fun E hE hEA => Certificates.certificate812462 E hE hEA

end CFSG.Monster.B.TwoA.Sp8.WordRel
