module

public import CFSG.Monster.B.Co2.Simple


public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.B.Short CFSG.Monster.B.Co2

theorem ncard_wOrbit_mul
    (x : Wv v0) :
    (wOrbit x).ncard * Nat.card (wStab x) = 42305421312000 := by
  rw [← index_wStab, Subgroup.index_mul_card, natCard_Kv]

end CFSG.Monster.B.TwoA
