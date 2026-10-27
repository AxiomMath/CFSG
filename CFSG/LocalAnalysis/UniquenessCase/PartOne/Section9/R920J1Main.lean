module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvableQ
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920J1Bar
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920J1Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddY9
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataThree
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920ShapeJ1
import CFSG.LocalAnalysis.UniquenessCase.UC22S215KF7UseThree
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (StronglyEmbeddedThree StronglyEmbeddedFive StronglyEmbeddedSolvableQ)

variable {G : Type} [Group G] [Finite G]

theorem r920J1_of_inputs (D : Data G) (hK3 : StronglyEmbeddedThree) (hK : UCK.K332Cyc)
    (hK32 : UCK.K32) (hK461 : UCK.K461) (hK462 : UCK.K462)
    (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) (h82 : F08.R82 D) (hSg : UC6S846.SigmaStd D)
    (h614 : UC6.R6_14 D) (h76 : F07.R76Sig D) (hKF7 : KF7Use D) : R920J1 D := by
  intro L D₃ Y H hyp hYL hJ
  have S : SliceCore D L D₃ Y H := ⟨hyp, hYL, Shape919.of_isJ1 hJ⟩
  obtain ⟨E, hE⟩ := S.exists_hyp91 hK3 hK h82 hSg h614 h76 hKF7
  exact S.false_of_isJ1 hK32 hK461 hK462 hSch hJ hE

theorem r920J1_dataOfSetup (hSQ : StronglyEmbeddedSolvableQ) (hSE : StronglyEmbeddedFive)
    (hK3 : StronglyEmbeddedThree) (hK : UCK.K332Cyc) (hK32 : UCK.K32) (hK461 : UCK.K461)
    (hK462 : UCK.K462) (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (hS : RankThreeUC.Standing G) (S : RankThreeUC.Setup G)
    (h82 : F08.R82 (PartTwo.Three.dataOfSetup hS S))
    (h614 : UC6.R6_14 (PartTwo.Three.dataOfSetup hS S)) :
    R920J1 (PartTwo.Three.dataOfSetup hS S) :=
  r920J1_of_inputs _ hK3 hK hK32 hK461 hK462 hSch h82 (UC6S846.sigmaStd_dataOfSetup hS S) h614
    (PartTwo.Three.r76Sig_dataOfSetup hSE hK3 hS S) (kf7Use_dataOfSetup hSQ hSE hK3 hS S)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9
