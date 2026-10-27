module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S215Setup4
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2115N
import CFSG.LocalAnalysis.UniquenessCase.UC22S2115NTwo
import CFSG.LocalAnalysis.UniquenessCase.UC22R82Four
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (StronglyEmbeddedFive StronglyEmbeddedSolvableQ StronglyEmbeddedThree BadNoStrongThree)

variable {G : Type} [Group G] [Finite G]

theorem s21_5_of_s21_15N_setup4 (hSQ : StronglyEmbeddedSolvableQ) (hSE : StronglyEmbeddedFive)
    (hK3 : StronglyEmbeddedThree) (hB3 : BadNoStrongThree) (hKThin : KThinSimple)
    (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G) (hMS : S.InMSigma)
    (hPart : PartIAt S.M) {Ch : Choice2011 G} :
    S21_15N (UC6.dataOfSetup4 hS hU S) Ch → S21_5 (UC6.dataOfSetup4 hS hU S) Ch := fun h15 =>
  s21_5_setup4 hSQ hSE hK3 hB3 hKThin hS hU S hMS (r82_dataOfSetup4 hS hU S hPart.2.2)
    (s21_15Two_of_s21_15N (UC6S846.sigmaStd_dataOfSetup4 hS hU S).nonempty h15)

end CFSG.LocalAnalysis.UniquenessCase.UC22
