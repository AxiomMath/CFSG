module

public import CFSG.LocalAnalysis.UniquenessCase.OpenThree.R82Exits
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.R82Setup
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.Case812Setup
public import CFSG.LocalAnalysis.UniquenessCase.UC22R880J4OfG
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R880J4GThree
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneL62Holds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three

open CFSG.LocalAnalysis.RankThreeUC (Setup Standing AGL81TheoremC)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (StronglyEmbeddedThree_of_KIB StronglyEmbeddedThreeKIB_of_small KIB3Small_holds)

variable {G : Type} [Group G] [Finite G]

theorem r82_dataOfSetup
    (hGF : CFSG.Yardstones.Me2c15c2c995a.GF2nCatalogClause) (hS : Standing G)
    (hUC : CFSG.Open.rankThreeUC G) (hC : AGL81TheoremC G) (S : Setup G) (hMS : S.InMSigma) :
    UC22.F08.R82 (dataOfSetup hS S) :=
  PartOne.Theorem82E3.r82_dataOfSetup_of_exits hGF PartOne.Theorem82E3.onanExcludedSetup_holds
    PartOne.Theorem82E3.l62ExcludedSetup_of_certificates
    (PartOne.Theorem82E3.case812Setup_of_scExcluded PartOne.Theorem82E3.scExcludedSetup_holds)
    hS hUC hC S hMS

theorem r880J4_dataOfSetup
    (hS : Standing G) (hUC : CFSG.Open.rankThreeUC G)
    (hC : AGL81TheoremC G) (S : Setup G) :
    UC22.F08.R880J4 (dataOfSetup hS S) :=
  have hG3 := RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
  have hSE3 := StronglyEmbeddedThree_of_KIB hG3 CFSG.AGLEmbedding.kFactCatalogSchreier_holds
    (StronglyEmbeddedThreeKIB_of_small hG3 KIB3Small_holds)
  UC22.F08.r880J4_of_r880J4G (UC6S846.sigmaStd_dataOfSetup hS S)
    (r76Sig_dataOfSetup PartOne.Section7.SEFive.stronglyEmbeddedFive_holds hSE3 hS S)
    (r880J4G_dataOfSetup hS hUC hC S)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three
