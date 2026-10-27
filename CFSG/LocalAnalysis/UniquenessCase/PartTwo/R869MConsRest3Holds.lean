module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R869MConsThree
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69R873
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xKOutPComplement
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.PartOneSixThirtyEight

public section

open CFSG.LocalAnalysis.RankThreeUC (Setup Standing)

variable {G : Type} [Group G] [Finite G]

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

theorem outPComplement_holds
    : OutPComplement :=
  fun _ _ _ hq hcat _ hp hp2 h1 =>
    hasNormalPComplement_outer_of_quasisimple_of_pRank_le_one hq hcat hp hp2 h1

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F08

theorem r869MConsRest3_of_outPComplement {D : Data G} (hSg : UC6S846.SigmaStd D)
    (h638 : UC6.R6_38 D) (hOut : PartOne.Section8.OutPComplement) : R869MConsRest3 D := by
  intro L hL hML _ _ hσ _
  exfalso
  obtain ⟨p, hp⟩ := hSg.nonempty
  obtain ⟨h1, -, hno⟩ := hσ p hp
  obtain ⟨A, hAM, hAel, hAc, hAL⟩ :=
    PartOne.Section8.r873_centralizing hSg h638 hOut hL hML hp h1
  exact hno A hAM hAel hAc hAL

end CFSG.LocalAnalysis.UniquenessCase.UC22.F08

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three

theorem r869MConsRest3_dataOfSetup
    (hS : Standing G) (S : Setup G) : UC22.F08.R869MConsRest3 (dataOfSetup hS S) :=
  UC22.F08.r869MConsRest3_of_outPComplement (UC6S846.sigmaStd_dataOfSetup hS S)
    (r6_38_dataOfSetup hS S) PartOne.Section8.outPComplement_holds

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three
