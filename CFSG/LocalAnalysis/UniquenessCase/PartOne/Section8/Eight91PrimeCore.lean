module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91Defs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91PrimeCoreD4
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91PrimeCoreSmall

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8


theorem r891PrimeCore_holds : R891PrimeCore :=
  ⟨fun _ _ _ _ h => R891Core.primeCore_d4 h, fun _ _ _ _ h => R891Core.primeCore_sl3Two h,
    fun _ _ _ _ h _ hp hp2 => R891Core.primeCore_l2 h hp hp2⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
