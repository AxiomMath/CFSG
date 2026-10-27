module

public import Certificates.Data.Y2L.Words
public import CFSG.RankThree.PartTwo.Census.Carrier.G2ThreeData
public import Mathlib

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec2

open CFSG.RankThree.PartTwo.Census.Carrier.G2Three

@[expose] def y2l_ngCodes (_ : Unit := ()) : List (List ℕ) :=
  [[0, 7, 3, 7, 4, 3, 3, 0, 3, 0, 2, 6, 5, 7, 5, 7, 0],
   [1, 4, 2, 1, 3, 1, 2, 4, 1, 3, 3, 6, 4, 7, 1],
   [1, 4, 0, 4, 7, 3, 7, 1, 2, 1, 3],
   [1, 4, 0, 4, 7, 3, 7, 3, 3, 1, 3, 0, 5, 3, 6, 4, 6, 5, 2, 1],
   [6, 4, 6, 1, 7, 2, 0, 2, 7, 1, 4, 1]]

@[expose] def y2l_ngW (_ : Unit := ()) : List (List ℕ) :=
  (y2l_ngCodes ()).map fun w =>
    w.flatMap fun c => List.replicate (if c % 2 = 0 then 1 else 2) (c / 2)

@[expose] def y2l_ngGen (i : ℕ) : List ℕ := [x0c, x1c, y0c, y1c].getD i one14

@[expose] def y2l_ngWord (w : List ℕ) : List ℕ :=
  w.foldl (fun acc i => mul14 acc (y2l_ngGen i)) one14

@[expose] def y2l_ngInv (w : List ℕ) : List ℕ := w.reverse.flatMap fun i => [i, i]

@[expose] def y2l_ngSubst (W : List (List ℕ)) (r : List (Fin 5 × Bool)) : List ℕ :=
  r.flatMap fun l => if l.2 then W.getD l.1 [] else y2l_ngInv (W.getD l.1 [])

@[expose] def y2l_ngCheck (_ : Unit := ()) : Bool :=
  let W := y2l_ngW ()
  [0, 1, 2, 3].all (fun i => y2l_ngWord [i, i, i] == one14) &&
    (y2l_ws26 1 true).all (fun r => y2l_ngWord (y2l_ngSubst W r) == one14) &&
    (y2l_ws7 1).all (fun r => y2l_ngWord (y2l_ngSubst W r) != one14)

end CFSG.OddStandard.HigherRank.G2Three.Sec2
