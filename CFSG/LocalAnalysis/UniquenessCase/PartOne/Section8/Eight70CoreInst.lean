module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight70Core
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Conclusion76Three
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72.Setup4Core
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72.Bad
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Theorem76

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (Sec7Core4 StronglyEmbeddedFive BadNoStrongThree)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)

variable {G : Type} [Group G] [Finite G]

theorem sec7CoreOdd_dataOfSetup (hSE : StronglyEmbeddedFive)
    (hS : CFSG.LocalAnalysis.RankThreeUC.Standing G) (hUC : CFSG.Open.rankThreeUC G)
    (hC : CFSG.LocalAnalysis.RankThreeUC.AGL81TheoremC G)
    (S : CFSG.LocalAnalysis.RankThreeUC.Setup G) :
    Sec7CoreOdd (CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three.dataOfSetup hS S) := by
  intro q hq hq2 hsp
  let k : Sec7Core4 G := Sec7Core4.ofThree hS S.M S.witness.maxLocal q hq hq2 hsp
    (CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three.normalizer_le_of_agl81TheoremC hUC hC S hq
      hq2 hsp)
  exact ⟨k, rfl, rfl, fun hq5 =>
    ⟨k.kIDExcluded_of_evenRank_le_three (le_of_eq hS.rank), k.step75 hq5 hSE⟩⟩

theorem sec7CoreOdd_dataOfSetup4 (hSE : StronglyEmbeddedFive) (hB : BadNoStrongThree)
    (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G) (hMS : S.InMSigma)
    (hPart : PartIAt S.M) :
    Sec7CoreOdd (CFSG.LocalAnalysis.UniquenessCase.UC6.dataOfSetup4 hS hU S) := by
  intro q hq hq2 hsp
  let k : Sec7Core4 G := Section7.R72.setup4Core hS hU S hPart q hq hq2 hsp
  exact ⟨k, rfl, rfl, fun hq5 =>
    ⟨Section7.R72.kIDExcluded_of_setup4 hU S hMS hB k rfl hq5, k.step75 hq5 hSE⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
