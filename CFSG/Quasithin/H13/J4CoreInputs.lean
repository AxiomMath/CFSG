
module

public import CFSG.Quasithin.H13.J4WordsBase
public import CFSG.Certificates.ExtraspecialNormalForm
public meta import Certificates.Data.CFSGNative.H13.J4Elems
public meta import CFSG.Quasithin.H13.J4Defs

public noncomputable section

namespace CFSG.Quasithin.H13.J4

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Quasithin.H13.J4.Native

open CFSG.Certificates.ExtraspecialNF

@[expose] def qIdx : List (List ℕ) :=
  [[0, 1], [0, 2], [0, 3], [1, 4], [0, 5], [1, 6], [0, 7], [2, 8], [0, 9], [1, 10], [2, 11],
    [0, 2, 3]]

@[expose] def cRows : List ℕ := [888, 3532, 2354, 179, 3149, 77, 3635, 522, 1031, 3265, 850, 598]

@[expose] def rExpr : List (ℕ × List ℕ) :=
  [(0, [1, 2, 11]), (1, [0, 1, 2, 11]), (1, [2, 11]), (0, [1, 11]), (0, [0, 1, 2, 3, 11]),
    (0, [1, 2, 4, 11]), (0, [0, 1, 2, 5, 11]), (0, [1, 2, 6, 11]), (0, [2, 7, 11]),
    (1, [1, 2, 8, 11]), (1, [0, 1, 2, 9, 11]), (0, [2, 10, 11])]

@[expose] def rPairs : Array Pr :=
  (List.range 12).toArray.map fun i =>
    rConjOf (uvPairsOf basePairs) (coreBasisConjugators.getD i [])

@[expose] def rProdPair (l : List ℕ) : Pr :=
  l.foldl (fun acc i => prMul acc (rPairs[i]?.getD prOne)) prOne

@[expose] def qProdPair (l : List ℕ) : Pr :=
  l.foldl (fun acc a => prMul acc (rProdPair (qIdx.getD a []))) prOne

@[expose] def pChecks : Bool :=
  let tP := tOf (uvPairsOf basePairs)
  let qs := (List.range 12).map fun a => rProdPair (qIdx.getD a [])
  (List.range 12).all (fun a => eqRows (mulRows (qs.getD a prOne).1 (qs.getD a prOne).1) idRows) &&
  (List.range 12).all (fun a => (List.range 12).all fun b =>
    eqRows (mulRows (qs.getD a prOne).1 (qs.getD b prOne).1)
      (if (cRows.getD a 0).testBit b
        then mulRows (mulRows (qs.getD b prOne).1 (qs.getD a prOne).1) tP.1
        else mulRows (qs.getD b prOne).1 (qs.getD a prOne).1)) &&
  (List.range 12).all fun i =>
    eqRows (rPairs[i]?.getD prOne).1
      (if ((rExpr.getD i (0, [])).1 = 1)
        then mulRows tP.1 (qProdPair (rExpr.getD i (0, [])).2).1
        else (qProdPair (rExpr.getD i (0, [])).2).1)

end CFSG.Quasithin.H13.J4
