module

public import CFSG.RankThree.PartTwo.Toolkit.M12LocalInputs
public import Certificates.Data.Kernel.M12Cent

public section

namespace CFSG.KC.M12Loc

open CFSG.GH74.M12.Hyp CFSG.KC.M12Cent CFSG.RankThree.PartTwo.Toolkit.M12

@[expose] def fixN (t : List ℕ) : ℕ := ((List.range 12).filter fun i => t.getD i 0 == i).length

@[expose] def nodupB : List ℕ → Bool
  | [] => true
  | a :: l => !l.contains a && nodupB l

@[expose] def prodR (TT : List (List (List ℕ))) (k : Idx) : List ℕ :=
  tmul ((TT.getD 0 []).getD k.1 tid) (tmul ((TT.getD 1 []).getD k.2.1 tid)
    (tmul ((TT.getD 2 []).getD k.2.2.1 tid) (tmul ((TT.getD 3 []).getD k.2.2.2.1 tid)
      ((TT.getD 4 []).getD k.2.2.2.2 tid))))

@[expose] def centerOK : Bool :=
  P0T.all fun s => !(tmul s xT == tmul xT s && tmul s yT == tmul yT s) || s == tid || s == zT ||
    s == tpow zT 2

@[expose] def aFixOK : Bool := AT.all fun s => fixN s != fixN zT || s == zT || s == tpow zT 2

@[expose] def listOK (p : List ℕ → Bool) (TT : List (List (List ℕ))) (L : List Idx)
    (T : List (List ℕ)) : Bool :=
  L.map (prodR TT) == T && nodupB (T.map keyT) && T.all p

@[expose] def countOK (q : List ℕ → Bool) (T : List (List ℕ)) (n : ℕ) : Bool :=
  (T.filter q).length == n

@[expose] def npOK (T : List (List ℕ)) : Bool :=
  T.all fun t => !predN [xT, yT] P0T t ||
    (P0T.contains (tmul t t) && predN [zT, xT] ET t && predN [zT, yT] FT t)

@[expose] def keyA (u : List ℕ) : ℕ := min (keyT u) (keyT (tmul u u))

@[expose] def orbOK (W : List (List ℕ)) : Bool :=
  W.length == 1320 && incr (W.map fun w => keyA (conjN w aT))

@[expose] def psiRows (R T : List (List ℕ)) : Bool :=
  R.all fun s => T.all fun t =>
    rowTab (tmul s t) == tmul (rowTab s) (rowTab t) &&
      colTab (tmul s t) == tmul (colTab s) (colTab t) &&
      (!(rowTab s == rowTab t && colTab s == colTab t) || s == t)

@[expose] def T3L : List (List ℕ) :=
  [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]]

@[expose] def T4eL : List (List ℕ) :=
  [[0, 1, 2, 3], [0, 2, 3, 1], [0, 3, 1, 2], [1, 0, 3, 2], [1, 2, 0, 3], [1, 3, 2, 0], [2, 0, 1, 3],
    [2, 1, 3, 0], [2, 3, 0, 1], [3, 0, 2, 1], [3, 1, 0, 2], [3, 2, 1, 0]]

@[expose] def psiValOK (T : List (List ℕ)) : Bool :=
  T.all fun s => T3L.contains (rowTab s) && T4eL.contains (colTab s)

end CFSG.KC.M12Loc

end
