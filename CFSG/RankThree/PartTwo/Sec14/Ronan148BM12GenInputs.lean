module

public import CFSG.RankThree.PartTwo.Sec4.Sporadic.M12SigCheckInputs

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148B.M12Gen

open CFSG.GH74.M12.Hyp CFSG.RankThree.PartTwo.Toolkit.M12 CFSG.RankThree.PartTwo.Sec4.Sporadic.M12Sig

@[expose] def vGensT : List (List ℕ) :=
  [[3, 5, 9, 0, 8, 1, 11, 10, 4, 2, 7, 6], [4, 6, 10, 8, 0, 11, 1, 9, 3, 7, 2, 5],
    [8, 11, 7, 4, 3, 6, 5, 2, 0, 10, 9, 1], [5, 10, 8, 4, 3, 0, 11, 9, 2, 7, 1, 6],
    [6, 7, 3, 2, 8, 11, 0, 1, 4, 10, 9, 5], [11, 9, 4, 8, 2, 6, 5, 10, 3, 1, 7, 0],
    [7, 4, 5, 8, 1, 2, 11, 0, 3, 10, 9, 6], [9, 8, 6, 4, 3, 11, 2, 10, 1, 0, 7, 5],
    [10, 3, 11, 1, 8, 6, 5, 9, 4, 7, 0, 2]]

@[expose] def wordA : List ℕ := [1, 5, 0, 4, 0, 3, 2, 6, 1, 4, 7, 3, 8, 5, 2, 8, 3]

@[expose] def wordB : List ℕ := [0, 8, 0, 4, 7, 1, 8, 4, 8, 3, 6, 0, 8, 5, 2, 4, 8, 5, 1]

@[expose] def wprod (w : List ℕ) : List ℕ := w.foldr (fun i acc => tmul (vGensT.getD i tid) acc) tid

@[expose] def genCheck (_ : Unit := ()) : Bool :=
  ((List.range 9).all fun k => (VT (k / 3)).contains (vGensT.getD k tid)) &&
    wprod wordA == tA && wprod wordB == tB &&
    (List.range 3).all fun i =>
      (VT i).all fun u => (VT i).any fun v => AT.any fun f => u == tcm v f

end CFSG.RankThree.PartTwo.Sec14.Ronan148B.M12Gen
