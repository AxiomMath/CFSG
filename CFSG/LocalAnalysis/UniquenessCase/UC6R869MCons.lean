module

public import CFSG.LocalAnalysis.UniquenessCase.UC6R869MConj
public import CFSG.LocalAnalysis.RankThreeTheoremC.OutCyclicThree

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 TheoremCAt)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedFive C76Three)

variable {G : Type} [Group G] [Finite G]

theorem r869MCons_dataOfSetup4 (hSE : StronglyEmbeddedFive) (hS : Standing4 G)
    (hU : uniqueFourUnique G) (S : Setup4 G) (hσ : S.InMSigma) (hC76 : C76Three S)
    (hC : TheoremCAt S.M) (h77 : F07.R77E4 (dataOfSetup4 hS hU S)) :
    F08.R869MCons (dataOfSetup4 hS hU S) :=
  r869MCons_dataOfSetup4_of_kFactOutCyclic
    CFSG.LocalAnalysis.RankThreeTheoremC.kFactOutCyclic_holds hSE hS hU S hσ hC76 hC h77

theorem r117W_dataOfSetup4 (hSE : StronglyEmbeddedFive) (hS : Standing4 G)
    (hU : uniqueFourUnique G) (S : Setup4 G) (hσ : S.InMSigma) (hC76 : C76Three S)
    (hC : TheoremCAt S.M) (h77 : F07.R77E4 (dataOfSetup4 hS hU S)) :
    R117W (dataOfSetup4 hS hU S) :=
  uc22p22u_c117W_of_R869MCons _ (r869MCons_dataOfSetup4 hSE hS hU S hσ hC76 hC h77)

end CFSG.LocalAnalysis.UniquenessCase.UC6
