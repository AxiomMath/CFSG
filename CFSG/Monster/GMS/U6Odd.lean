module

public import CFSG.Monster.GMS.U6OddCo1

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

namespace U6Odd

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ : G}

theorem eightOneOddOrder_of
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) :
    EightOneOddOrder a z₀ :=
  eightOneOddOrder_of_co1 I hG u6OddFact

end U6Odd

end CFSG.Monster.GMS
