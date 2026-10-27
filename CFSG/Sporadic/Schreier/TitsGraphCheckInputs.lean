module

public import CFSG.Sporadic.Schreier.TitsActionCheck
public import Certificates.Data.CFSGNative.SectionRank.TitsChain
public meta import CFSG.Sporadic.Schreier.TitsData
public meta import CFSG.Sporadic.Schreier.TitsArrays
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import CFSG.Sporadic.Schreier.TitsCertCheck
public meta import CFSG.Sporadic.Schreier.TitsActionCheck
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import Certificates.Data.CFSGNative.SectionRank.TitsChain

public section

namespace CFSG.Sporadic.Schreier.Tits

open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native

@[expose] def titsNbrData : Array (List (ℕ × ℕ)) :=
  (List.range 2925).foldl (fun acc v =>
    [(0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1)].foldl (fun acc kk =>
      acc.modify titsLinePtArr[3 * v + kk.1]! fun l => l ++ [(titsLinePtArr[3 * v + kk.2]!, v)])
      acc) (Array.replicate 1755 [])

@[expose] def titsNbr : Array (Array ℕ) :=
  titsNbrData.map fun l => ((l.map Prod.fst).mergeSort fun a b => decide (a ≤ b)).toArray

@[expose] def titsNbrLine : Array (Array ℕ) :=
  titsNbrData.map fun l => ((l.mergeSort fun a b => decide (a.1 ≤ b.1)).map Prod.snd).toArray

@[expose] def ptsHas (v u : ℕ) : Bool :=
  titsLinePtArr[3 * v]! == u || titsLinePtArr[3 * v + 1]! == u || titsLinePtArr[3 * v + 2]! == u

@[expose] def nbrColors (col : Array ℕ) (x : ℕ) : List ℕ :=
  ((titsNbr[x]!).toList.map fun w => col[w]!).mergeSort fun a b => decide (a ≤ b)

@[expose] def sigCode (col : Array ℕ) (x : ℕ) : ℕ :=
  (nbrColors col x).foldl (fun acc a => acc * 1756 + a) col[x]!

@[expose] def dedupSorted : List ℕ → List ℕ
  | a :: b :: l => if a = b then dedupSorted (b :: l) else a :: dedupSorted (b :: l)
  | l => l

@[expose] def sortedValues (v : Array ℕ) : Array ℕ :=
  (dedupSorted (v.toList.mergeSort fun a b => decide (a ≤ b))).toArray

@[expose] def relabel (v : Array ℕ) : Array ℕ :=
  v.map fun a => CFSG.SectionRank.Native.Tits.bsearch (sortedValues v) a

@[expose] def refineStep (col : Array ℕ) : Array ℕ :=
  relabel (Array.ofFn (n := 1755) fun x => sigCode col x)

@[expose] def titsIndiv : List ℕ := [1, 3, 6, 5, 12, 24]

@[expose] def initColor (i : ℕ) : Array ℕ := Array.ofFn (n := 1755) fun x =>
  if (titsIndiv.take i).contains (x : ℕ) then (titsIndiv.take i).idxOf (x : ℕ) + 1 else 0

@[expose] def titsRounds : List ℕ := [0, 3, 6, 7, 6, 6, 6]

@[expose] def stableColor (i : ℕ) : Array ℕ := Nat.iterate refineStep titsRounds[i]! (initColor i)

@[expose] def numCells (col : Array ℕ) : ℕ := (sortedValues col).size

@[expose] def cellSize (col : Array ℕ) (x : ℕ) : ℕ :=
  ((List.range 1755).filter fun y => col[y]! == col[x]!).length

@[expose] def titsCellSizes : List ℕ := [1755, 80, 8, 2, 4, 4]

@[expose] def titsCellCounts : List ℕ := [1, 5, 25, 86, 149, 477, 1755]

@[expose] def refineOK (i : ℕ) (col : Array ℕ) : Bool :=
  col.size == 1755 && numCells col == titsCellCounts[i]! &&
    numCells (refineStep col) == numCells col &&
    (i == 6 || cellSize col titsIndiv[i]! == titsCellSizes[i]!)

end CFSG.Sporadic.Schreier.Tits
