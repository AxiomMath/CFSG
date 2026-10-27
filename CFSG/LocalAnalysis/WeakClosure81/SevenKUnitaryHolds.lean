module

public import CFSG.LocalAnalysis.WeakClosure81.SevenKUnitaryFour
import CFSG.LocalAnalysis.WeakClosure81.EightFiveRootRankU3Holds

public section

namespace CFSG.LocalAnalysis.WeakClosure81

theorem unitaryRootCommutatorRank_holds :
    SevenK.UnitaryRootCommutatorRank := by
  refine unitaryRootCommutatorRank_iff_at.2 fun m hm => ?_
  rcases Nat.lt_or_ge m 4 with h | h
  · obtain rfl : m = 3 := by omega
    exact unitaryRootCommutatorRankAt_three_of_irreducible su3IrreducibleRank_holds
  · exact unitaryRootCommutatorRankAt_of_four_le h

end CFSG.LocalAnalysis.WeakClosure81

end
