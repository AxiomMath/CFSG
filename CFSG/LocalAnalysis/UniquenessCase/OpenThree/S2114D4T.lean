module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114D4K1Three
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91R891Three
import CFSG.LocalAnalysis.UniquenessCase.UC7R71Three
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SigmaRankThree13

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.RankThreeUC (Setup Standing AGL81TheoremC)

variable {G : Type} [Group G] [Finite G]


theorem s21_14D4T_dataOfSetup (hS : Standing G) (hUC : CFSG.Open.rankThreeUC G)
    (hC : AGL81TheoremC G) (S : Setup G) (hMS : S.InMSigma) :
    S21_14D4T (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) :=
  s21_14D4T_of_r891 (UC6S846.sigmaStd_dataOfSetup hS S)
    (fun L hL f _ hD => PartOne.Section8.r891_dataOfSetup_of_d4Core hS hUC hC S hMS L hL f hD)
    (s21_14D4TK1_of_facts (UC6S846.sigmaStd_dataOfSetup hS S)
      (PartTwo.Three.sigmaRankThree13_dataOfSetup hS hUC S)
      (fun _ hq hq2 => PartTwo.Three.pRank_le_three_dataOfSetup hS S hq hq2 le_rfl)
      (PartTwo.Three.r71_dataOfSetup hS S (PartTwo.Three.r6_3_dataOfSetup hS hUC hC S))
      (PartOne.Section7.R72.r72_dataOfSetup hS hUC hC S) kStrongEmbedded72_holds)

end CFSG.LocalAnalysis.UniquenessCase.UC22
