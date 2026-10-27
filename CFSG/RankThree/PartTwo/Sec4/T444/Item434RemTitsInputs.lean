module

public import CFSG.Sporadic.Schreier.TitsStabCheckInputs
public import CFSG.Sporadic.Schreier.TitsInvCheckInputs

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434RemTits

open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits

@[expose] def xWord : List ℤ :=
  [10, 5, -13, 2, -1, -7, 10, 5, -13, 2, -1, -7, 10, 5, -13, 2, -1, -7, 10, 5, -13, 2, -1, -7]

@[expose] def yWord : List ℤ := [2, -12, 4, 5, -11, -2] ++ xWord ++ [2, 11, -5, -4, 12, -2]

@[expose] def zWord : List ℤ := [-11, -2, -3, -6] ++ xWord ++ [6, 3, 2, 11]

@[expose] def powWord (w : List ℤ) : ℕ → List ℤ
  | 0 => []
  | k + 1 => w ++ powWord w k

@[expose] def sylWords : List (List ℤ) :=
  (List.range 27).map fun k => powWord xWord (k / 9) ++ powWord yWord (k / 3 % 3) ++
    powWord zWord (k % 3)

@[expose] def sylArrs : List (Array ℕ) := sylWords.map (wordArr 1755 titsDerivedArrs)

@[expose] def fixCount (n : ℕ) (a : Array ℕ) : ℕ := (List.range n).countP fun i => a[i]! == i

@[expose] def lineOK (w : List ℤ) : Bool :=
  eqA 1755 (wordArr 1755 titsDerivedArrs w) (idA 1755) ||
    (fixCount 2925 (wordArr 2925 titsTStarArrs w) % 5 != 0 &&
      fixCount 2925 (wordArr 2925 titsTStarArrs w) % 13 != 0)

@[expose] def bOneWord : List ℤ := [12, -2, -9] ++ xWord ++ [9, 2, -12]

@[expose] def bOneArr : Array ℕ := wordArr 1755 titsDerivedArrs bOneWord

@[expose] def invTest (a : Array ℕ) : Bool :=
  !(commA a titsTArr && commA a bOneArr && eqA 1755 (compA 1755 a a) (idA 1755)) ||
    eqA 1755 a (idA 1755) || eqA 1755 a titsTArr

end CFSG.RankThree.PartTwo.Sec4.Item434RemTits
