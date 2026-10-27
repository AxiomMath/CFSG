module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvableQ
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddGt7
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddMain
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataThree
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddFrob
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQ7
import CFSG.LocalAnalysis.UniquenessCase.UC22S215KF7UseThree
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R92b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (StronglyEmbeddedThree StronglyEmbeddedFive StronglyEmbeddedSolvableQ)

variable {G : Type} [Group G] [Finite G]

theorem r920odd_of_kfacts (D : Data G)
    (hK3 : StronglyEmbeddedThree) (hK : UCK.K332Cyc) (hK32 : UCK.K32) (hK461 : UCK.K461)
    (hK462 : UCK.K462) (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes)
    (hGA : CFSG.Open.GriessAllModelsStatement) (hZ : UCK.ZassenhausPerfect)
    (h82 : F08.R82 D) (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) (h76 : F07.R76Sig D)
    (hKF7 : KF7Use D) : R920odd D :=
  r920odd_of_inputs D hK3 hK h82 hSg h614 h76 hKF7
    (fun _ _ _ _ _ Sl hq _ hE hN =>
      Sl.false_of_hN_gt_seven hq hN hE hK32 hK461 hK462 hSch hSp hGA hZ)
    (fun _ _ Y H _ Sl hq E hE hN => by
      have h92 := F09.r92_of_inputs hK32 hSch D Y H E hE Sl.H_ne_top
      exact Sl.false_of_hN_eq_seven hq hN hE h92.1 h92.2
        (Sl.I9_le_M_of_odd_dvd hN hE ⟨3, Nat.prime_three, by norm_num, by rw [hq]; norm_num⟩
          hK461 hK462 hSch))

theorem r920odd_dataOfSetup (hSQ : StronglyEmbeddedSolvableQ)
    (hSE : StronglyEmbeddedFive) (hK3 : StronglyEmbeddedThree) (hK : UCK.K332Cyc)
    (hK32 : UCK.K32) (hK461 : UCK.K461) (hK462 : UCK.K462)
    (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes)
    (hGA : CFSG.Open.GriessAllModelsStatement) (hZ : UCK.ZassenhausPerfect)
    (hS : RankThreeUC.Standing G) (S : RankThreeUC.Setup G)
    (h82 : F08.R82 (PartTwo.Three.dataOfSetup hS S))
    (h614 : UC6.R6_14 (PartTwo.Three.dataOfSetup hS S)) :
    R920odd (PartTwo.Three.dataOfSetup hS S) :=
  r920odd_of_kfacts _ hK3 hK hK32 hK461 hK462 hSch hSp hGA hZ h82
    (UC6S846.sigmaStd_dataOfSetup hS S) h614 (PartTwo.Three.r76Sig_dataOfSetup hSE hK3 hS S)
    (kf7Use_dataOfSetup hSQ hSE hK3 hS S)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9
