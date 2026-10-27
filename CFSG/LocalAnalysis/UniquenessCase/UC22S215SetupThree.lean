module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S215KF7UseThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsFive
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229KOut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (StronglyEmbeddedFive StronglyEmbeddedSolvableQ StronglyEmbeddedThree)

variable {G : Type} [Group G] [Finite G]

theorem s21_5_dataOfSetup (hSQ : StronglyEmbeddedSolvableQ) (hSE : StronglyEmbeddedFive)
    (hK3 : StronglyEmbeddedThree) (hKThin : KThinSimple) (hS : RankThreeUC.Standing G)
    (S : RankThreeUC.Setup G) {Ch : Choice2011 G}
    (h82 : F08.R82 (PartTwo.Three.dataOfSetup hS S))
    (h15 : S21_15Two (PartTwo.Three.dataOfSetup hS S) Ch) :
    S21_5 (PartTwo.Three.dataOfSetup hS S) Ch :=
  s21_5_of' _ _ (UC6S846.sigmaStd_dataOfSetup hS S) (kf7Use_dataOfSetup hSQ hSE hK3 hS S) h82 h15
    hKThin KBridge.kOddOutInner_holds

end CFSG.LocalAnalysis.UniquenessCase.UC22
