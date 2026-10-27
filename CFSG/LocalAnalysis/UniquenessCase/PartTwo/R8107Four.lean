module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R8107U3
public import CFSG.LocalAnalysis.UniquenessCase.UC22R82Four
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229KThin
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SlotsFourAssembly
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3ThreeKIBA6

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Four

open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)

variable {G : Type} [Group G] [Finite G]


theorem r8107_dataOfSetup4
    (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G)
    (S : Setup4 G) (hMS : S.InMSigma) (hPart : PartIAt S.M) :
    F08.R8107 (UC6.dataOfSetup4 hS hU S) :=
  r8107_of_inputs _ (dataExt_ofSetup4 hS hU S) (by have := hS.rank; omega)
    (UC6S846.sigmaStd_dataOfSetup4 hS hU S) (r82_dataOfSetup4 hS hU S hPart.2.2)
    (r76Sig_dataOfSetup4 PartOne.Section7.SEFive.stronglyEmbeddedFive_holds
      (PartOne.Section7.StronglyEmbeddedThree_of_KIB
        CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
        CFSG.AGLEmbedding.kFactCatalogSchreier_holds
        (PartOne.Section7.StronglyEmbeddedThreeKIB_of_small
          CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
          PartOne.Section7.KIB3Small_holds))
      PartOne.Section7.badNoStrongThree_holds hS hU S hMS)
    ((UC6.r6_14_dataOfSetup4_iff hS hU S).2 hPart.2.1) KBridge.kThinSimple_holds

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Four
