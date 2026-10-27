module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs15
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem r129_1_of_r127 (D : UC22.Data G) (h127 : R127 D) : R129_1 D :=
  fun _ _ h => (twelve_nine D h127 h).1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
