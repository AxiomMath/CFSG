module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Conclusion76Three
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07Use
import CFSG.LocalAnalysis.UniquenessCase.UC6R77Three

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three

open CFSG.LocalAnalysis.RankThreeUC
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedFive StronglyEmbeddedThree)

variable {G : Type} [Group G] [Finite G]

theorem r77E2_dataOfSetup (hSE : StronglyEmbeddedFive) (hSE3 : StronglyEmbeddedThree)
    (hS : Standing G) (S : Setup G) : UC22.F07.R77E2 (dataOfSetup hS S) :=
  UC6.r77E2_of_conclusion76 _ fun p hp hsp =>
    r76Sig_dataOfSetup hSE hSE3 hS S p hp ((dataOfSetup hS S).sig_prime p hp).2 hsp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three
