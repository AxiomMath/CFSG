
module

public import CFSG.Quasithin.H13.J4CoreBase
public meta import CFSG.Quasithin.H13.J4CoreBase
public meta import CFSG.Quasithin.H13.J4Defs
public meta import Certificates.Data.CFSGNative.H13.J4Elems

public section

namespace CFSG.Quasithin.H13.J4

open CFSG.Sporadic.J4.Native CFSG.Quasithin.H13.J4.Native

@[expose] def ntWord : List ℤ := [2, 1, -2, 1, 2, 1, -2, 1, -2, 1, -2, 1]

@[expose] def w0Pair : Pr := prPow (prWord (uvPairsOf basePairs) ntWord) 11

@[expose] def tPair : Pr := tOf (uvPairsOf basePairs)

@[expose] def w0Check : Bool :=
  let r := rPairs[0]?.getD prOne
  let c := prMul (prMul (prMul w0Pair r) (prInv w0Pair)) (prInv r)
  rowsNe c.1 idRows && rowsNe c.1 tPair.1

@[expose] def hypA : List (List ℕ) :=
  [[0, 1], [1, 2], [0, 2, 3, 4, 5], [2, 3, 4, 6], [4, 5, 6, 7], [1, 3, 5, 9]]

@[expose] def hypB : List (List ℕ) :=
  [[1, 4], [0, 3], [0, 1, 2, 3, 4, 5], [1, 4, 5, 11], [0, 4, 5, 8], [2, 4, 5, 6, 8, 10]]

@[expose] def hypList (k : ℕ) : List ℕ := if k % 2 = 0 then hypA.getD (k / 2) [] else
  hypB.getD (k / 2) []

@[expose] def rExprH : List (List ℕ × ℕ) :=
  [([0, 4, 5], 0), ([4, 5], 1), ([2, 4, 5], 0), ([0, 3, 4, 5], 1), ([1, 4, 5], 0),
    ([1, 2, 3, 4], 0), ([0, 1, 2, 3, 4, 5, 6], 1), ([0, 1, 4, 6, 8], 1), ([0, 2, 3, 4, 9], 0),
    ([0, 1, 2, 4, 10], 1), ([1, 3, 4, 5, 6, 9, 11], 0), ([2, 3, 4, 7], 1)]

@[expose] def hypPair (k : ℕ) : Pr := rProdPair (hypList k)

@[expose] def hypProdPair (l : List ℕ) : Pr :=
  l.foldl (fun acc k => prMul acc (hypPair k)) prOne

@[expose] def plusChecks : Bool :=
  (List.range 6).all (fun i =>
    let a := hypPair (2 * i)
    let b := hypPair (2 * i + 1)
    eqRows (prMul a a).1 idRows && eqRows (prMul b b).1 idRows &&
      eqRows (prMul (prMul a b) (prMul a b)).1 tPair.1) &&
  (List.range 6).all fun i => (List.range 6).all fun j =>
    i == j ||
      (eqRows (prMul (hypPair (2 * i)) (hypPair (2 * j))).1
          (prMul (hypPair (2 * j)) (hypPair (2 * i))).1 &&
        eqRows (prMul (hypPair (2 * i)) (hypPair (2 * j + 1))).1
          (prMul (hypPair (2 * j + 1)) (hypPair (2 * i))).1 &&
        eqRows (prMul (hypPair (2 * i + 1)) (hypPair (2 * j + 1))).1
          (prMul (hypPair (2 * j + 1)) (hypPair (2 * i + 1))).1)

@[expose] def genChecks : Bool :=
  (List.range 12).all fun j =>
    let e := rExprH.getD j ([], 0)
    eqRows (rPairs[j]?.getD prOne).1 (prMul (prPow tPair e.2) (hypProdPair e.1)).1

@[expose] def weakWord : List ℤ := [-2, 1, 2, 1, 2, 2]

@[expose] def weakPair : Pr :=
  let g := prWord basePairs weakWord
  let s := prMul (prMul (prInv g) (hypPair 0)) g
  prMul (prPow (prMul tPair s) 6) (prInv g)

@[expose] def weakChecks : Bool :=
  eqRows (prMul (prMul (prInv weakPair) tPair) weakPair).1 (hypPair 0).1 &&
    rowsNe (hypPair 0).1 tPair.1

end CFSG.Quasithin.H13.J4
