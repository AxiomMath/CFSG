module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Steps87Four
public import Certificates.Certificate291400
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R4Holds
public import CFSG.LocalAnalysis.UniquenessCase.UC22GlobalsYNo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U7KFacts

import CFSG.LocalAnalysis.UniquenessCase.UCK35wHolds
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KIZHolds
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.Holds
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvableHolds
import CFSG.LocalAnalysis.UniquenessCase.UC7P3BadNoStrongHolds
import CFSG.LocalAnalysis.UniquenessCase.UC7P3ThreeKIBA6
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.StrongThree
import CFSG.LocalAnalysis.RankThreeTheoremC.OutCyclicThree
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CatalogSchreier
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CartanTorusU7
public import Certificates.Certificate9726
public import Certificates.Certificate17430
public import Certificates.Certificate431004

public import Certificates.Certificate8058
public import Certificates.Certificate8059
public import Certificates.Certificate9542
public import Certificates.Certificate9543
public import Certificates.Certificate12610
public import Certificates.Certificate12612
public import Certificates.Certificate12613
public import Certificates.Certificate12614
public import Certificates.Certificate12623
public import Certificates.Certificate12635
public import Certificates.Certificate12636
public import Certificates.Certificate12641
public import Certificates.Certificate428001
public import Certificates.Certificate428004
public import Certificates.Certificate12611
public import Certificates.Certificate12617
public import Certificates.Certificate12618
public import Certificates.Certificate12619
public import Certificates.Certificate12620
public import Certificates.Certificate12634
public import Certificates.Certificate12637
public import Certificates.Certificate13513
public import Certificates.Certificate13659
public import Certificates.Certificate13660
public import Certificates.Certificate24945
public import Certificates.Certificate24946

public import Certificates.Certificate7252

public import Certificates.Certificate1322003
public import Certificates.Certificate1322004
public import Certificates.Certificate1322005
public import Certificates.Certificate1322006
public import Certificates.Certificate1322007
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallAutFix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (StronglyEmbeddedFive StronglyEmbeddedThree StronglyEmbeddedSolvable BadNoStrongThree)



theorem steps86_dataOfSetup4_of_steps87 {G : Type} [Group G] [Finite G]
    (hKF1 : KFieldAutOdd) (hKS : KFunSplit) (hKC : KFunCount) (hKA : KLieBorelAutPrime)
    (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) (hPart : PartIAt S.M)
    (h : Steps87 (UC6.dataOfSetup4 hS hU S) (fun _ _ => True)) :
    Steps86 (UC6.dataOfSetup4 hS hU S) (fun _ _ => True) := by
  have hs := setup4S21Facts_dataOfSetup4 hS hU S hMS hPart h.s21_3Rest15
  have hgr := CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement
  have hSE : StronglyEmbeddedFive := PartOne.Section7.SEFive.stronglyEmbeddedFive_holds
  have hSS : StronglyEmbeddedSolvable := PartOne.Section7.stronglyEmbeddedSolvable_holds
  have hB3 : BadNoStrongThree := PartOne.Section7.badNoStrongThree_holds
  have hG3 := CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
  have hK3 : StronglyEmbeddedThree :=
    PartOne.Section7.StronglyEmbeddedThree_of_KIB hG3 CFSG.AGLEmbedding.kFactCatalogSchreier_holds
      (PartOne.Section7.StronglyEmbeddedThreeKIB_of_small hG3 PartOne.Section7.KIB3Small_holds)
  exact h.toSteps86 hKF1 hKS hKC hKA PartTwo.Inputs1719.k_U7CentTorus_holds
    PartTwo.Inputs1719.k_U7CartanSylowAbelian_holds hgr global22yNo_holds.nativeGriess
    UCK.k35w_holds PartOne.Section8.stronglyEmbeddedCentralFree_holds hS hU S hMS hPart
    hSE hSS hK3 hB3 CFSG.LocalAnalysis.RankThreeTheoremC.kFactOutCyclic_holds
    (fun _ _ => True) hs.kf7 hs.r76 hs.hn3 hs.s21_3 hs.s21_5 hs.s20_7 hs.r82 hs.s21_1
    (fun _ _ _ => trivial)




theorem steps86_dataOfSetup4
    {G : Type} [Group G] [Finite G]
    (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) (hPart : PartIAt S.M) :
    Steps86 (UC6.dataOfSetup4 hS hU S) (fun _ _ => True) :=
  steps86_dataOfSetup4_of_steps87 kFieldAutOdd_holds kFunSplit_holds kFunCount_holds
    kLieBorelAutPrime_holds hS hU S hMS hPart (steps87_dataOfSetup4 hS hU S hMS hPart)

end CFSG.LocalAnalysis.UniquenessCase.UC22
