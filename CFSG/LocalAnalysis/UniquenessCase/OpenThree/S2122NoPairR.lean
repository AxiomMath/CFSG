module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2122NPRed
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SigmaRankThree13

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.RankThreeUC (Setup Standing AGL81TheoremC)

variable {G : Type} [Group G] [Finite G]

theorem s21_22R3NoPairR_dataOfSetup (hS : Standing G) (hUC : CFSG.Open.rankThreeUC G)
    (_hC : AGL81TheoremC G) (S : Setup G) (_hMS : S.InMSigma)
    (hSE3 : PartOne.Section7.StronglyEmbeddedThree)
    (h211 : S21_1 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True))
    (hn3 : H1930 (PartTwo.Three.dataOfSetup hS S) →
      ∀ c : Ctx21 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True), 3 ≤ c.n)
    (h218 : S21_8N (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True))
    (h218UR : S21_8UR (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True)) :
    S21_22R3NoPairR (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) :=
  s21_22R3NoPairR_of_inputs (UC6S846.sigmaStd_dataOfSetup hS S) hSE3 h211 hn3 h218 h218UR
    fun _ hr h7 h3 => PartTwo.Three.mem_sigmaOf_of_three_le_pRank hS hUC S.witness.maxLocal hr h7 h3

end CFSG.LocalAnalysis.UniquenessCase.UC22
