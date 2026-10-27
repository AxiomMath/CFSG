module

public import CFSG.RankThree.PartTwo.KFacts.KS21AutThreeL44
public import CFSG.RankThree.PartTwo.KFacts.KS21AutThreeSp64
public import CFSG.RankThree.PartTwo.KFacts.KS21AutThreeU58

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS21

theorem terminalAutThree : TerminalAutThree :=
  ⟨U58.autThree_projSU, L44.autThree_projSL, Sp64.autThree_projSp⟩

theorem terminalSylowThree : TerminalSylowThree :=
  terminalSylowThree_of_autThree terminalAutThree

end CFSG.RankThree.PartTwo.KFacts.KS21
