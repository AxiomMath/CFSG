module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qzb
public import CFSG.LocalAnalysis.UniquenessCase.UC22Standing22
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.PartOneThreeSix
import CFSG.LocalAnalysis.UniquenessCase.UC611f
import CFSG.LocalAnalysis.UniquenessCase.UC22P21m
import CFSG.LocalAnalysis.UniquenessCase.UC22P22za
import CFSG.LocalAnalysis.UniquenessCase.UC6S6
import CFSG.LocalAnalysis.UniquenessCase.UC6Star36b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open (rankThreeUC)
open CFSG.LocalAnalysis.RankThreeUC (AGL81TheoremC)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 TheoremCAt)

variable {G : Type} [Group G] [Finite G]

theorem Standing22.ofSetup4 (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) (hC : TheoremCAt S.M) (hK : UCK.K36)
    (hF : Frob4Prime (UC6.dataOfSetup4 hS hU S)) : Standing22 (UC6.dataOfSetup4 hS hU S) where
  dataExt := dataExt_ofSetup4 hS hU S
  sigmaStd := UC6S846.sigmaStd_dataOfSetup4 hS hU S
  sigma23 := sigma23Std_ofSetup4 hS hU S
  sigma2 := sigma2Print_ofSetup4 hS hU S (frob4_of_frob4Prime hF)
  cent := r613cent_ofSetup4 hS hU S
  r6_1 := UC6.r6_1_dataOfSetup4 hS hU S
  r6_3 := UC6.r6_3_dataOfSetup4 hS hU S hC
  r6_6 := UC6.r6_6_dataOfSetup4 hS hU S hMS hC
  r6_7 := PartTwo.r6_7_of_K36_at (UC6.dataOfSetup4 hS hU S) hK (UC6.r6_3_dataOfSetup4 hS hU S hC)
    (UC6.star36_holds G hS hU S hMS hC)
  r6_11 := UC6.r6_11Used_of_sig3_eq_empty rfl
  three_mem_sig := uc22p21m_hsig3_ofSetup4 hS hU S hMS

theorem Standing22.ofSetup (hS : RankThreeUC.Standing G) (hUC : rankThreeUC G)
    (hC : AGL81TheoremC G) (hK : UCK.K36) (S : RankThreeUC.Setup G) (hMS : S.InMSigma) :
    Standing22 (PartTwo.Three.dataOfSetup hS S) where
  dataExt := dataExt_ofSetup hS S
  sigmaStd := UC6S846.sigmaStd_dataOfSetup hS S
  sigma23 := sigma23Std_ofSetup hS S
  sigma2 := sigma2Print_ofSetup hS S
  cent := r613cent_ofSetup hS S
  r6_1 := PartTwo.Three.r6_1_dataOfSetup hS S
  r6_3 := PartTwo.Three.r6_3_dataOfSetup hS hUC hC S
  r6_6 := PartTwo.Three.r6_6_dataOfSetup hS hUC hC S
  r6_7 := PartTwo.Three.r6_7_dataOfSetup hS hUC hC hK S
  r6_11 := UC6.r6_11Used_dataOfSetup hS S
  three_mem_sig := uc22p21m_hsig3_ofSetup hS S hMS

end CFSG.LocalAnalysis.UniquenessCase.UC22
