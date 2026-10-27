module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveFourteenSetup
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5ASTwelve
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.PartOneThreeSix
public import CFSG.LocalAnalysis.UniquenessCase.UC6S6

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.RankThreeUC
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 TheoremCAt)

variable {G : Type} [Group G] [Finite G]

theorem r1214_ofSetup_AS (hS : Standing G) (hUC : rankThreeUC G)
    (hC : AGL81TheoremC G) (S : Setup G) (h5_11 : WeakClosure81.Asch5_11AS)
    (h5_13 : WeakClosure81.Asch5_13AS)
    (h127 : R127 (Three.dataOfSetup hS S)) (h861 : W3Lem86_1 G)
    (hTim : CFSG.CGT.Timmesfeld75.NodeStatement) : F12.R1214 (Three.dataOfSetup hS S) := by
  exact r1214_ofSetup_of_r126 hS S
    (WeakClosure81.r126_of_twelve_six_AS _ h5_11 h5_13 (Three.r6_6_dataOfSetup hS hUC hC S))
    h127 h861 hTim

theorem r1214_ofSetup4_AS (hS : Standing4 G)
    (hU : uniqueFourUnique G) (S : Setup4 G) (hMS : S.InMSigma) (hC : TheoremCAt S.M)
    (h5_11 : WeakClosure81.Asch5_11AS) (h5_13 : WeakClosure81.Asch5_13AS)
    (h127 : R127 (UC6.dataOfSetup4 hS hU S)) (h861 : W3Lem86_1 G)
    (hTim : CFSG.CGT.Timmesfeld75.NodeStatement) : F12.R1214 (UC6.dataOfSetup4 hS hU S) := by
  exact r1214_ofSetup4_of_r126 hS hU S
    (WeakClosure81.r126_of_twelve_six_AS _ h5_11 h5_13
      (UC6.r6_6_dataOfSetup4 hS hU S hMS hC)) h127 h861 hTim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
