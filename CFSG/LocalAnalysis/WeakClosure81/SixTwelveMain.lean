module

public import CFSG.LocalAnalysis.WeakClosure81.SixTwelveQuotC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Close

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

section Certified


theorem w3Lem612_holds : W3Lem612 G :=
  fun h hd => h.inCalOStar hd

end Certified

end CFSG.LocalAnalysis.WeakClosure81
