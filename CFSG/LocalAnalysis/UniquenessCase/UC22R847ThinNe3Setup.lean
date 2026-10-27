module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R847ThinNe3
public import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3Thin
public import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3NNTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.RankThreeUC (Standing Setup)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedFive
  StronglyEmbeddedFiveZ StronglyEmbeddedSolvableQ StronglyEmbeddedThree)
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (Gls3StronglyThreeEmbeddedPlus)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three (dataOfSetup)

variable {G : Type} [Group G] [Finite G]

theorem r847ThinNe3_dataOfSetup
    (hSE : StronglyEmbeddedFive) (hSEZ : StronglyEmbeddedFiveZ) (hThin : PartTwo.ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian)
    (hSQ : StronglyEmbeddedSolvableQ) (hK3 : StronglyEmbeddedThree)
    (hG3 : Gls3StronglyThreeEmbeddedPlus) (hRee : CFSG.AGLEmbedding.KFactReeInvolution)
    (hS : Standing G) (S : Setup G) : R847ThinNe3 (dataOfSetup hS S) := by
  intro Y hY hthin X hXY q hq hq2 hXc p hp hp3
  by_cases hYN : (Y.subgroupOf (dataOfSetup hS S).M).Normal
  · rcases r847E3Thin_dataOfSetup hSE hSEZ hThin hCyc hG3 hRee hK3 hS S Y hY hYN hthin X hXY q
      hq hq2 hXc p hp with h | ⟨h3, -⟩
    · exact h
    · exact absurd h3 hp3
  · exact r847E3ThinNNTwo_dataOfSetup hSE hSEZ hThin hSQ hK3 hG3 hRee hS S Y hY hYN hthin X hXY q
      hq hq2 hXc p hp fun h => absurd h hp3

end CFSG.LocalAnalysis.UniquenessCase.UC22
