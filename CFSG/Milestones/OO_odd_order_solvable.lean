module

public import CFSG.FeitThompson.OddOrderTheorem

public section

universe u v w

namespace CFSG.OddOrder

theorem _root_.CFSG.Milestones.odd_order_solvable {G : Type*} [Group G] [Finite G]
    (_h : Odd (Nat.card G)) : Group.IsSolvable G :=
  CFSG.FeitThompson.isSolvable_of_odd_natCard _ _h

end CFSG.OddOrder
