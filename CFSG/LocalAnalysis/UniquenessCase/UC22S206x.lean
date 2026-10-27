module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S206w
public import CFSG.LocalAnalysis.UniquenessCase.UC22R82Four
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.RankThree.PartOne.TCB.SchreierFinal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedFive)


theorem s20_6_dataOfSetup4_of_k331 {G : Type} [Group G] [Finite G] (hK331 : InS3.K331)
    (hSE : StronglyEmbeddedFive) (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G)
    (S : Setup4 G) (hσ : S.InMSigma) (hPart : PartIAt S.M) : S20_6 (UC6.dataOfSetup4 hS hU S) :=
  uc22s206w_s20_6 hS hU S hσ CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
    listBNonabelian hK331 CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds
    uc22p20r_nativeGriess (r82_dataOfSetup4 hS hU S hPart.2.2) hSE

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
