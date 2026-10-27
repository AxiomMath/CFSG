module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72.FourCore
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallOutPPrime
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.Holds
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3BadNoStrongHolds
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72.ReeThreeType
import CFSG.LocalAnalysis.UniquenessCase.UC7P3ReeU3Excl

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72

variable {G : Type} [Group G] [Finite G]

section


theorem r72_dataOfSetup4
    (hS : CFSG.Yardstones.Mf4cdcdf2e013.Standing4 G)
    (hU : CFSG.Open.uniqueFourUnique G) (S : CFSG.Yardstones.Mf4cdcdf2e013.Setup4 G)
    (hMS : S.InMSigma) (hPart : CFSG.Yardstones.Mf4cdcdf2e013.PartIAt S.M) :
    CFSG.LocalAnalysis.UniquenessCase.UC22.F07.R72
      (CFSG.LocalAnalysis.UniquenessCase.UC6.dataOfSetup4 hS hU S) :=
  r72_dataOfSetup4_of UCK.kFactSmallIdent_holds UCK.kFactOneLieIdent_holds
    UCK.stronglyEmbeddedCyclicOuter_holds
    (CFSG.AGLEmbedding.kFactSmallOutPPrime_of_smallIdent UCK.kFactSmallIdent_holds)
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group (fun _ _ _ => isReeType_one_of_psl28)
    SEFive.stronglyEmbeddedFive_holds badNoStrongThree_holds
    (fun k _ hH hp3 => k.exists_rows3_of_config
      CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
      CFSG.AGLEmbedding.kFactReeInvolution hp3 hH)
    hS hU S hMS hPart

end

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72
