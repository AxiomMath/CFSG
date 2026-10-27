module

public import Certificates.Data.GH74.Ivk8Weak
public meta import Certificates.Data.GH74.Ivk8Weak

public section

namespace Certificates.Ivk8Two

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Schreier
  CFSG.Certificates Certificates.Odd87F3 Certificates.Ivk8Weak

@[expose] def dataRels : List (List ℤ × List ℤ) := [
  ([1, 1], []), ([2, 2], []), ([3, 3], []), ([4, 4], []),
  ([2, 3], [3, 2]), ([2, 4], [4, 2]), ([2, 1], [1, 2]), ([3, 4], [4, 3]), ([3, 1], [1, 3]),
  ([4, 1], [1, 4]), ([1, 5], [5, 1]), ([1, 6], [6, 1]),
  ([5, 2], [2, 1, 5]), ([5, 3], [4, 1, 5]), ([5, 4], [3, 1, 5]),
  ([-5, 2], [2, 1, -5]), ([-5, 3], [4, 1, -5]), ([-5, 4], [3, 1, -5]),
  ([6, 2], [2, 6]), ([6, 3], [3, 1, 6]), ([6, 4], [2, 4, 1, 6]),
  ([-6, 2], [2, -6]), ([-6, 3], [3, 1, -6]), ([-6, 4], [2, 4, 1, -6]),
  ([5, 5], [1]), ([6, 6], [1]), ([5, 6, 5, 6, 5, 6, 5, 6], [1])]

@[expose] def w8Words : List (List ℤ) :=
  [[], [5], [6], [5, 6], [6, 5], [5, 6, 5], [6, 5, 6], [5, 6, 5, 6]]

@[expose] def allDistinct (n : ℕ) : List Table → Bool
  | [] => true
  | t :: ts => ts.all (fun s => !tblEq n t s) && allDistinct n ts

@[expose] def twoTables (n : ℕ) (gT : List Table) (wa w₁ w₂ w₃ wx wy : List ℤ) : List Table :=
  let gIT := gT.map (invT n)
  [evalT n gT gIT wa, evalT n gT gIT w₁, evalT n gT gIT w₂, evalT n gT gIT w₃,
    evalT n gT gIT wx, evalT n gT gIT wy]

@[expose] def twoProds (n : ℕ) (ts : List Table) : List Table :=
  let its := ts.map (invT n)
  let V := subprodsT n (ts.take 4)
  (w8Words.map (evalT n ts its)).flatMap fun w => V.map (compT n w)

@[expose] def twoOKT (n : ℕ) (gT : List Table) (wa w₁ w₂ w₃ wx wy : List ℤ) : Bool :=
  let ts := twoTables n gT wa w₁ w₂ w₃ wx wy
  let its := ts.map (invT n)
  gT.all (fun g => invOK n g (invT n g)) && ts.all (fun t => invOK n t (invT n t)) &&
    dataRels.all (fun r => tblEq n (evalT n ts its r.1) (evalT n ts its r.2)) &&
    !tblEq n (ts.headD (idT n)) (idT n) && (twoProds n ts).length == 128 &&
    allDistinct n (twoProds n ts)

@[expose] def centralOKT (n : ℕ) (gT : List Table) (w : List ℤ) : Bool :=
  let t := evalT n gT (gT.map (invT n)) w
  gT.all (fun g => invOK n g (invT n g)) && gT.all (fun g => tblEq n (compT n t g) (compT n g t))

end Certificates.Ivk8Two
