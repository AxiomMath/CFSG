module

public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229N
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
public import CFSG.LocalAnalysis.UniquenessCase.UC6Inst
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputs
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229G898
import CFSG.LocalAnalysis.UniquenessCase.UCKP3
import CFSG.LocalAnalysis.UniquenessCase.UCKPFI3
import CFSG.LocalAnalysis.UniquenessCase.UCKP898D
import CFSG.LocalAnalysis.UniquenessCase.UCKP898F
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsNine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsNineTorus
import CFSG.LocalAnalysis.UniquenessCase.Lie.SU3Cover
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 TheoremCAt)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedFive)

variable {G : Type} [Group G] [Finite G]


theorem s21_9N_setup4_of_r847 (hSE : StronglyEmbeddedFive) (hS : Standing4 G)
    (hU : uniqueFourUnique G) (S : Setup4 G) (hσ : S.InMSigma) (hC : TheoremCAt S.M)
    (hgr : GriessAllModelsStatement) (h846 : F08.R846 (UC6.dataOfSetup4 hS hU S))
    (h847 : F08.R847 (UC6.dataOfSetup4 hS hU S)) {Ch : Choice2011 G}
    (h211 : S21_1 (UC6.dataOfSetup4 hS hU S) Ch) : S21_9N (UC6.dataOfSetup4 hS hU S) Ch :=
  s21_9N_of_s21_9NFull (s21_9NFull_of _ Ch (dataExt_ofSetup4 hS hU S).sig_nonempty h211 h846 h847
    (UC6S898.r898_full _ (UC6S846.sigmaStd_dataOfSetup4 hS hU S) h846 (UCK.u3Center_of_griess hgr)
        UCK.u3Range (UCK.u3FixInner_of_griess hgr) (UCK.u3FixField_holds hgr)
        (UCK.u3Trio_of_griess hgr).1 (UCK.u3Fix3Field_holds hgr) (UCK.u3Trio_of_griess hgr).2.1
        (UCK.u3Trio_of_griess hgr).2.2
        (r898Gamma_setup4 hSE hS hU S hσ (UCK.u3Center_of_griess hgr))
        (UC6.r6_3_dataOfSetup4 hS hU S hC))
    (s21_9TorusN_of _ Ch uc22pwCartanSU3_holds))

end CFSG.LocalAnalysis.UniquenessCase.UC22
