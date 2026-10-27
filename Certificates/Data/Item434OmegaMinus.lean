module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEightMinus.NativeData

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434OmegaMinus

open CFSG.EvenSmallLie.OmegaEightMinus CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.EvenSmallLie.OmegaEight (pushWords wordsOf)

@[expose] def linApply (cols : List ℕ) (v : ℕ) : ℕ :=
  (List.range 8).foldl (fun r i => if v.testBit i then r ^^^ cols.getD i 0 else r) 0

@[expose] def linArr (cols : List ℕ) : Array ℕ :=
  Array.ofFn (n := 136) fun i => nsIdx[linApply cols nsArr[i.val]!]!

@[expose] def zCols : List (List ℕ) :=
  [[1, 2, 4, 8, 16, 32, 128, 192], [1, 16, 48, 8, 54, 20, 64, 128],
    [1, 20, 54, 8, 6, 4, 64, 128]]

@[expose] def tCols : List ℕ := [1, 164, 86, 8, 178, 214, 18, 38]

@[expose] def sCols : List (List ℕ) :=
  [[73, 2, 4, 1, 16, 32, 129, 64], [27, 54, 49, 1, 17, 21, 64, 128],
    [31, 48, 55, 1, 34, 33, 64, 128]]

@[expose] def zArr (i : ℕ) : Array ℕ := linArr (zCols.getD i [])

@[expose] def tArr : Array ℕ := linArr tCols

@[expose] def sArrs : Array (Array ℕ) := (sCols.map linArr).toArray

@[expose] def vecArr (a b c : ℕ) : Array ℕ :=
  compA 136 (compA 136 (powArr (zArr 0) a) (powArr (zArr 1) b)) (powArr (zArr 2) c)

@[expose] def omegaLevels : Array Level := rawLevels 136 omegaS (omegaBase.map Fin.val).toArray

@[expose] def memOK (g : Array ℕ) : Bool :=
  isInvA 136 g (invCand 136 g) && siftA 136 omegaLevels (omegaBase.map Fin.val).toArray 0 g

@[expose] def eltsCheck : Bool :=
  allLt 3 (fun i => memOK (zArr i)) && memOK tArr && allLt 3 (fun k => memOK sArrs[k]!)

@[expose] def wreathCheck : Bool :=
  allLt 3 (fun i => eqA 136 (powArr (zArr i) 3) (idA 136)) &&
    allLt 3 (fun i => allLt 3 fun j => commArr (zArr i) (zArr j)) &&
    eqA 136 (powArr tArr 3) (idA 136) &&
    allLt 3 (fun i => eqA 136 (conjArr tArr (zArr i)) (zArr ((i + 1) % 3))) &&
    allLt 3 (fun a => allLt 3 fun b => allLt 3 fun c =>
      (a == 0 && b == 0 && c == 0) || !eqA 136 (vecArr a b c) (idA 136)) &&
    allLt 3 (fun a => allLt 3 fun b => allLt 3 fun c => !eqA 136 (vecArr a b c) tArr)

@[expose] def centCheck : Bool :=
  allLt 3 (fun k => eqA 136 (powArr sArrs[k]! 5) (idA 136)) &&
    allLt 3 (fun k => allLt 3 fun i => i == k || commArr sArrs[k]! (zArr i))

@[expose] def genWords : List (List ℤ) :=
  [[-1, -2, 3, 1], [-4, -4], [-1, 4, 1], [-6, -6], [-1, 6, 1], [-8, -8], [-2, -1, 3, 2],
    [-6, 8, -10, 6], [-9, 11, 5], [-7, -11, 12, 7], [-13, -12], [-14, -14], [-13, 15, 12],
    [-14, -16, 14, 16], [-17, -15]]

@[expose] def genS : Array (Array ℕ) := pushWords 136 sArrs genWords

@[expose] def genBase : List (Fin 136) := [0, 1, 4, 2, 5, 12, 28]

@[expose] def genChainCheck : Bool :=
  rawChainOK 136 (genS.extract 0 3) genS (genBase.map Fin.val).toArray (wordsOf 3 genWords) 4 &&
    rawOrbitSizes 136 genS (genBase.map Fin.val).toArray == [136, 63, 32, 15, 4, 4, 3]

end CFSG.RankThree.PartTwo.Sec4.Item434OmegaMinus
