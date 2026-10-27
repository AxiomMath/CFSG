module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataThree
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2Cases
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2D4Rank
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2D4Section
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2G2Exc
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2D4Exc
import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitHolds
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.RankThreeUC (Setup Standing AGL81TheoremC)

variable {G : Type} [Group G] [Finite G]

theorem s21_12aFR34F2Even2_dataOfSetup
    (hGA : CFSG.Open.GriessAllModelsStatement) (hS : Standing G) (S : Setup G)
    (hKF7 : KF7Use (PartTwo.Three.dataOfSetup hS S))
    (hn3 : H1930 (PartTwo.Three.dataOfSetup hS S) →
      ∀ c : Ctx21 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True), 3 ≤ c.n)
    (h5 : S21_5 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True))
    (h82 : F08.R82 (PartTwo.Three.dataOfSetup hS S))
    (h211 : S21_1 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True)) :
    S21_12aFR34F2Even2 (PartTwo.Three.dataOfSetup hS S)
      (Choice214U (PartTwo.Three.dataOfSetup hS S)) :=
  s21_12aFR34F2Even2_of_exc kFunSplit_holds hGA (UC6S846.sigmaStd_dataOfSetup hS S) hKF7 hn3 h5
    h82 h211 (fun _ _ _ => trivial) uc22ExcTwoFun_g2 uc22ExcTwoFunWeak_trialityD4
    triD4OuterThreeRank_holds triD4OuterThreeSection_holds

end CFSG.LocalAnalysis.UniquenessCase.UC22
