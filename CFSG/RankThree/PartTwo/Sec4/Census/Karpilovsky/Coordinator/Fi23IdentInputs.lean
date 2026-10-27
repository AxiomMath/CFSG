module

public import CFSG.Sporadic.Presentation.Fi23Inputs

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

@[expose] def t23Letter (i : ℕ) : ℕ := [7, 6, 5, 0, 1, 2, 3, 8, 9, 4].getD i 0

@[expose] def t23Words : List (List ℕ) :=
  CFSG.Sporadic.Presentation.Fi23.R0.map fun w => w.map fun l => t23Letter l.1.val

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three
