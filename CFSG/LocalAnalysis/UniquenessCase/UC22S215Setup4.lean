module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S215KF7UseFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsFive
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229KOut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (StronglyEmbeddedFive StronglyEmbeddedSolvableQ StronglyEmbeddedThree BadNoStrongThree)

variable {G : Type} [Group G] [Finite G]

theorem s21_5_setup4 (hSQ : StronglyEmbeddedSolvableQ) (hSE : StronglyEmbeddedFive)
    (hK3 : StronglyEmbeddedThree) (hB3 : BadNoStrongThree) (hKThin : KThinSimple)
    (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G) (hMS : S.InMSigma)
    {Ch : Choice2011 G} (h82 : F08.R82 (UC6.dataOfSetup4 hS hU S))
    (h15 : S21_15Two (UC6.dataOfSetup4 hS hU S) Ch) :
    S21_5 (UC6.dataOfSetup4 hS hU S) Ch :=
  s21_5_of' _ _ (UC6S846.sigmaStd_dataOfSetup4 hS hU S)
    (kf7Use_dataOfSetup4 hSQ hSE hK3 hB3 hS hU S hMS) h82 h15 hKThin KBridge.kOddOutInner_holds

end CFSG.LocalAnalysis.UniquenessCase.UC22
