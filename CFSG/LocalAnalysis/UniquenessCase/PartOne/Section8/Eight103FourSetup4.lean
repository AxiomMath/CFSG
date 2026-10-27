module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight103FourRank
public import CFSG.LocalAnalysis.UniquenessCase.UC7R76Four
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
import CFSG.LocalAnalysis.UniquenessCase.UC22R82Four

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)

variable {G : Type} [Group G] [Finite G]

theorem r8103_dataOfSetup4 (hSE : PartOne.Section7.StronglyEmbeddedFive)
    (hSE3 : PartOne.Section7.StronglyEmbeddedThree) (hB : PartOne.Section7.BadNoStrongThree)
    (hKD : KU45KeyDvd) (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) (hPart : PartIAt S.M) : F08.R8103 (UC6.dataOfSetup4 hS hU S) := by
  intro L P p n hH
  exact (false_of_hyp8102_of_four_le_pRank (UC6S846.sigmaStd_dataOfSetup4 hS hU S)
    (F07.R76Sig_of_R76 _ (UC6.r76_dataOfSetup4 hSE hSE3 hB hS hU S hMS hPart))
    ((UC6.r6_14_dataOfSetup4_iff hS hU S).2 hPart.2.1)
    (r82_dataOfSetup4 hS hU S hPart.2.2) hKD hH
    (UC6.four_le_pRank_of_sigma hH.2.2.2.1)).elim

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

end
