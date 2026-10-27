
module

public import CFSG.Sporadic.Co2Schreier.ChainCheckBase
public import CFSG.Sporadic.Schreier.RuEnum
public meta import CFSG.Sporadic.Co2Schreier.ChainCheckBase
public meta import CFSG.Sporadic.Schreier.RuEnum

public section

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu
  CFSG.Sporadic.RuSchreier

@[expose] def prodArr (A : Array (Array ℕ)) (l : List ℕ) : Array ℕ :=
  l.foldl (fun acc i => compA 2300 acc A[i]!) (idA 2300)

@[expose] def sqArr (t : Array ℕ) : Array ℕ := compA 2300 t t

@[expose] def fratSpecs : List (List ℕ) :=
  [[2], [8], [9], [10], [11], [12], [14], [0, 13], [8, 13], [8, 14], [11, 13], [13, 14]]

@[expose] def fratOrig : Array (Array ℕ) := (fratSpecs.map fun l => sqArr (prodArr sArrs l)).toArray

@[expose] def fratDerivs : List (List ℤ) := [[-10, 12, 2], [-5, -12, 2], [-3, -10, 7, 4],
  [-4, -11, 6, 5]]

@[expose] def fratStrong : Array (Array ℕ) := extendArrs fratOrig fratDerivs

@[expose] def fratWords : Array (List ℤ) := (List.replicate 12 [] ++ fratDerivs).toArray

@[expose] def fratBase : Array ℕ := #[0, 1]

@[expose] def fratLevels : Array Level := rawLevels 2300 fratStrong fratBase

@[expose] def yBasisSpecs : List (List ℕ) := [[13], [3, 14], [9, 14], [11, 14], [9, 11, 14]]

@[expose] def yBasisArrs : Array (Array ℕ) := (yBasisSpecs.map (prodArr sArrs)).toArray

@[expose] def bits5 (w : ℕ) : List ℕ := (List.range 5).filter fun k => w.testBit k

@[expose] def yArr (w : ℕ) : Array ℕ := prodArr yBasisArrs (bits5 w)

@[noinline, expose] def fratCheck (lv : Array Level) : Bool :=
  rawChainOK 2300 fratOrig fratStrong fratBase fratWords 4 &&
    rawOrbitSizes 2300 fratStrong fratBase == [128, 64] &&
    allInv fratOrig && allInv fratStrong && fratOrig.size == 12 && yBasisArrs.size == 5 &&
    allLt 15 (fun j => allLt 12 fun k => siftA 2300 lv fratBase 0
      (compA 2300 (compA 2300 sArrs[j]! fratOrig[k]!) (invCand 2300 sArrs[j]!))) &&
    allLt 15 (fun i => allLt 15 fun j => siftA 2300 lv fratBase 0
      (compA 2300 (compA 2300 (compA 2300 sArrs[i]! sArrs[j]!) (invCand 2300 sArrs[i]!))
        (invCand 2300 sArrs[j]!))) &&
    allLt 15 (fun j => siftA 2300 lv fratBase 0 (sqArr sArrs[j]!)) &&
    allLt 32 (fun u => isInvA 2300 (yArr u) (invCand 2300 (yArr u))) &&
    allLt 32 (fun u => allLt 32 fun v => !(decide (u < v)) ||
      !siftA 2300 lv fratBase 0 (compA 2300 (invCand 2300 (yArr u)) (yArr v))) &&
    allLt 15 (fun j => commA zArr sArrs[j]!)

@[expose] def sqChain (x : Array ℕ) : ℕ → List (Array ℕ)
  | 0 => []
  | n + 1 => x :: sqChain (compA 2300 x x) n

@[expose] def firstIdx (p : Array ℕ → Bool) : List (Array ℕ) → ℕ
  | [] => 0
  | x :: l => if p x then 0 else firstIdx p l + 1

@[expose] def ordCode (x : Array ℕ) : ℕ := firstIdx (fun y => eqA 2300 y (idA 2300)) (sqChain x 6)

@[expose] def ordZCode (z x : Array ℕ) : ℕ :=
  firstIdx (fun y => eqA 2300 y (idA 2300) || eqA 2300 y z) (sqChain x 6)

@[expose] def profKey (z x : Array ℕ) : ℕ := ordCode x * 8 + ordZCode z x

@[expose] def keys2 (L : Array Level) (key : Array ℕ → ℕ) : List ℕ :=
  (List.range L[0]!.pts.size).flatMap fun a =>
    (List.range L[1]!.pts.size).map fun b => key (prod2A 2300 L a b)

@[expose] def profTable : List (List ℕ) := [
  [2, 1406, 6784, 0, 0, 0, 1, 1087, 6080, 1024, 0, 0],
  [0, 768, 7424, 0, 0, 0, 0, 640, 5504, 2048, 0, 0],
  [0, 0, 6144, 2048, 0, 0, 0, 0, 4096, 4096, 0, 0],
  [0, 0, 0, 8192, 0, 0, 0, 0, 0, 8192, 0, 0],
  [0, 512, 5632, 2048, 0, 0, 0, 512, 3584, 4096, 0, 0],
  [0, 0, 0, 8192, 0, 0, 0, 0, 0, 8192, 0, 0],
  [0, 1152, 7040, 0, 0, 0, 0, 960, 6208, 1024, 0, 0],
  [0, 512, 7680, 0, 0, 0, 0, 512, 5632, 2048, 0, 0],
  [0, 0, 6144, 2048, 0, 0, 0, 0, 6144, 2048, 0, 0],
  [0, 0, 4096, 4096, 0, 0, 0, 0, 4096, 4096, 0, 0],
  [0, 512, 5632, 2048, 0, 0, 0, 512, 5632, 2048, 0, 0],
  [0, 0, 4096, 4096, 0, 0, 0, 0, 4096, 4096, 0, 0],
  [0, 512, 5632, 2048, 0, 0, 0, 512, 5632, 2048, 0, 0],
  [0, 0, 4096, 4096, 0, 0, 0, 0, 4096, 4096, 0, 0],
  [0, 768, 5376, 2048, 0, 0, 0, 640, 5504, 2048, 0, 0],
  [0, 0, 8192, 0, 0, 0, 0, 0, 6144, 2048, 0, 0],
  [0, 512, 3584, 4096, 0, 0, 0, 256, 3840, 4096, 0, 0],
  [0, 0, 8192, 0, 0, 0, 0, 0, 6144, 2048, 0, 0],
  [0, 0, 4096, 4096, 0, 0, 0, 0, 2048, 6144, 0, 0],
  [0, 0, 0, 8192, 0, 0, 0, 0, 0, 8192, 0, 0],
  [0, 0, 4096, 4096, 0, 0, 0, 0, 2048, 6144, 0, 0],
  [0, 0, 0, 8192, 0, 0, 0, 0, 0, 8192, 0, 0],
  [0, 0, 4096, 4096, 0, 0, 0, 0, 2048, 6144, 0, 0],
  [0, 0, 0, 8192, 0, 0, 0, 0, 0, 8192, 0, 0],
  [0, 0, 8192, 0, 0, 0, 0, 0, 4096, 4096, 0, 0],
  [0, 0, 8192, 0, 0, 0, 0, 0, 4096, 4096, 0, 0],
  [0, 0, 4096, 4096, 0, 0, 0, 0, 2048, 6144, 0, 0],
  [0, 0, 0, 8192, 0, 0, 0, 0, 0, 0, 8192, 0],
  [0, 0, 4096, 4096, 0, 0, 0, 0, 2048, 6144, 0, 0],
  [0, 0, 0, 8192, 0, 0, 0, 0, 0, 0, 8192, 0],
  [0, 512, 7680, 0, 0, 0, 0, 256, 5888, 2048, 0, 0],
  [0, 512, 7680, 0, 0, 0, 0, 256, 5888, 2048, 0, 0]]

@[noinline, expose] def profileOK (lv : Array Level) (z : Array ℕ) (tbl : List (List ℕ)) :
    Bool :=
  allLt 32 fun w =>
    let ks := keys2 lv fun t => profKey z (compA 2300 (yArr w) t)
    allLt 6 fun e => (ks.map (· / 8)).count e == (tbl.getD w []).getD (6 + e) 0 &&
      (ks.map (· % 8)).count e == (tbl.getD w []).getD e 0

@[expose] def uniqueOK (tbl : List (List ℕ)) : Bool :=
  allLt 5 fun k => allLt 32 fun w => w == 2 ^ k || tbl.getD w [] != tbl.getD (2 ^ k) []

end CFSG.Sporadic.Co2Schreier
