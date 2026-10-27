module

public import CFSG.RankThree.PartTwo.Sec21.HeringRootsSp64
public import CFSG.RankThree.PartTwo.Sec21.HeringRootsU58
public import CFSG.RankThree.PartTwo.Sec21.Item233OneProofStatements

public section

namespace CFSG.RankThree.PartTwo.Sec21

theorem terminalRootComponents_holds : TerminalRootComponents := by
  intro G _ _ I A hAI hA hI D hD hDinv hDgen B hBA hB X hX
  rcases hI with hU | hL | hS
  · exact terminalRootComponentsU58 G I A hAI hA hU D hD hDinv hDgen B hBA hB X hX
  · exact terminalRootComponentsL44 G I A hAI hA hL D hD hDinv hDgen B hBA hB X hX
  · exact terminalRootComponentsSp64 G I A hAI hA hS D hD hDinv hDgen B hBA hB X hX

end CFSG.RankThree.PartTwo.Sec21
