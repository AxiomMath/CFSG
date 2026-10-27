module

public import CFSG.Sporadic.Schreier.TitsAbelCheck
public meta import CFSG.Sporadic.Schreier.TitsData
public meta import CFSG.Sporadic.Schreier.TitsArrays
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import CFSG.Sporadic.Schreier.TitsCertCheck
public meta import CFSG.Sporadic.Schreier.TitsLocalCheck
public meta import CFSG.Sporadic.Schreier.TitsEnum
public meta import CFSG.Sporadic.Schreier.TitsCentralCheck
public meta import CFSG.Sporadic.Schreier.TitsAbelCheck
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data

public section

namespace CFSG.Sporadic.Schreier.Tits

open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native

@[expose] def titsTWord : List ℤ := [-4, -4, 13, 13, -4, -4, -4, -4, 13, 13, -4, -4]

@[expose] def titsTArr : Array ℕ := wordArr 1755 titsDerivedArrs titsTWord

@[expose] def conjArr (g x : Array ℕ) : Array ℕ := compA 1755 (compA 1755 g x) (invCand 1755 g)

@[expose] def inH (a : Array ℕ) : Bool := siftA 1755 titsHLevels (baseArr 1755 titsHBase) 0 a

@[expose] def inN (a : Array ℕ) : Bool := siftA 1755 titsNLevels (baseArr 1755 titsNBase) 0 a

@[expose] def inK (a : Array ℕ) : Bool := siftA 1755 titsKLevels (baseArr 1755 titsKBase) 0 a

@[expose] def commA (a b : Array ℕ) : Bool := eqA 1755 (compA 1755 a b) (compA 1755 b a)

@[expose] def titsInvCert : List (Bool × List ℤ) := [
  (false, [-1, 13, -3, -1]), (false, [-3, 4, -13, 1]), (false, [10, 13, 1]), (true, [7, -1]),
  (false, [13, 7, 1]), (false, [-13, -4, 3, 1]), (false, [2, -1, 5, 1]), (false, [10, 13, 3, 1]),
  (true, [2, 9, -2]), (false, [6, 2, -5, -1]), (false, [-3, 13]), (false, [-5, 13, 1]),
  (true, [2, 10, -2]), (false, [5, 1]), (false, [13, -3]), (false, [-13, 1]),
  (true, [-4, 13, 4, 1]), (false, [-13, -1, 5, 1]), (false, [13, 3, 4]), (false, [-1, 11, 1]),
  (false, [10, -13, 1]), (false, [-1, 12, 1]), (false, [4, 13]), (false, [4]),
  (false, [4, -13, 7, 1]), (false, [-2, 11, 2]), (false, [3, 4, 1]), (false, [2, -10, -2]),
  (true, [2, 8, -2]), (false, [2, -5, -1, 5]), (false, [5, 2, 8, -2]), (false, [13, 7, 3, 1]),
  (false, [5]), (false, [3, 13]), (false, [-4, -13, 1]), (true, [2, -10, -2]),
  (false, [6, -1, 5, 1]), (false, [11, 1]), (true, [13, -1]), (false, [-3, -13, 3, 1]),
  (true, [4, 1, 10, -1]), (true, [4, 10, 13, 1]), (false, [11, 3, 1]), (false, [-4, 13, 3]),
  (false, [13, 13, 3, 1]), (false, [-13, -4]), (false, [-13, 10, 1]), (false, [2, 10, -2]),
  (false, [-1, 13, -3]), (true, [-1, 3, 1]), (false, [-1, 11, 3, 1]), (false, [-1, 10, 1]),
  (false, [-7, -13, 1]), (true, [-5, -1]), (true, [10, -1]), (false, [13, 5]),
  (false, [4, 13, 1]), (true, [3, -1, 3, 1]), (true, [-7, -1]), (false, [-13, 5, 1]),
  (false, [13, 12, 1]), (true, [1, 11, 5, -2]), (false, []), (false, [-4, 13, 7, 1]),
  (false, [-4, -13, 12, 1]), (false, [10, 3, 1]), (false, [4, -13, 1]), (false, [-13, 7, 3, 1]),
  (false, [7, 1]), (false, [-13, 4, 1]), (false, [-4, 3, 1]), (false, [-3, -13, 1]),
  (false, [1]), (false, [-13, 3, 1]), (false, [13, 4, 1]), (false, [7, -13, 1]),
  (false, [7, 5, 1]), (false, [-13, 3, 4, 1]), (false, [3, -13, 4, 1]), (false, [3, 4]),
  (true, [2, 2, -4, 2]), (false, [3]), (false, [2, -5, -1]), (false, [4, 13, 4, 1]),
  (false, [-1, -13, 4]), (false, [-13, -4, 1]), (false, [-4]), (false, [-1, 5, 1]),
  (false, [-13, -13, 1]), (false, [3, -13, 7, 1]), (true, [1, 5, -2]), (false, [7, 3, 1]),
  (false, [-13, 7, 1]), (false, [-4, 1]), (false, [2, 8, -2]), (false, [13, 3]),
  (true, [1, 10, -1]), (false, [3, 10, -13, 1]), (false, [-13, -13, 3, 1]), (false, [-3, 13, 1]),
  (true, [-3, -1, 3, 1]), (false, [13, 13, 4, 1]), (false, [4, -13, 3, 1]),
  (true, [-3, 1, 5, -2]), (false, [13]), (false, [-4, 13]), (false, [3, -13, 1]),
  (false, [-3, 13, 4, 1]), (false, [13, 5, 1]), (false, [-1, 6, 1, 1]), (false, [-4, -13, 3, 1]),
  (false, [-2, -11, 2]), (false, [4, 1]), (false, [4, 3, 1]), (false, [5, 13, 1]),
  (false, [6, -1, 10, 1]), (false, [-13, 4]), (false, [10, -4, -13, 1]), (false, [-13, 12, 1]),
  (false, [-4, 13, 4, 1]), (false, [13, 10, 1]), (false, [13, 1]), (true, [4, -1, 3, 1]),
  (false, [7, -13, 4, 1]), (true, [3, -13, 4, 1]), (false, [-3, 13, 3, 1]),
  (false, [-13, 11, 1]), (true, [-1]), (false, [10, 1]), (true, []), (false, [-4, 13, 5, 1]),
  (false, [10, 3]), (false, [-2, 9, 2]), (false, [3, 1]), (true, [6, -1]), (false, [-3]),
  (true, [2, -7, -1]), (false, [13, 11, 1]), (false, [12, 1]), (false, [13, 3, 1]),
  (false, [13, 4, 3, 1]), (false, [13, 13, 1]), (true, [5, -1])]

@[expose] def titsInvConj : List (Array ℕ) :=
  titsInvCert.map fun bw =>
    conjArr (wordArr 1755 titsDerivedArrs bw.2) (if bw.1 then titsZArr else titsTArr)

@[expose] def titsFixWords : List (ℕ × List ℤ) := [
  (0, []), (1, [-3, 1, 5, -2]), (2, [-1, 3, 1]), (3, [4, -1, 3, 1]), (4, [1, 11, 5, -2]),
  (5, [1, 5, -2]), (6, [13, -1]), (7, [3, -1, 3, 1]), (8, [6, -1]), (9, [-3, -1, 3, 1]),
  (10, [7, -1]), (11, [2, -7, -1]), (13, [2, 2, -4, 2]), (14, [5, -1]), (15, [-4, 13, 4, 1]),
  (17, [1, 10, -1]), (18, [10, -1]), (19, [2, 8, -2]), (21, [2, 9, -2]), (25, [4, 1, 10, -1]),
  (26, [-1]), (31, [-7, -1]), (32, [3, -13, 4, 1]), (37, [2, 10, -2]), (46, [-5, -1]),
  (57, [4, 10, 13, 1]), (68, [2, -10, -2])]

@[expose] def titsExcl : List (Array ℕ) :=
  (titsFixWords.filter fun pw => 2 < pw.1).map fun pw =>
    compA 1755 (compA 1755 (invCand 1755 (wordArr 1755 titsDerivedArrs pw.2)) titsTArr)
      (wordArr 1755 titsDerivedArrs pw.2)

@[expose] def titsCHt : List (Array ℕ) := survivors5 1755 titsHLevels fun a => commA a titsTArr

@[expose] def titsCNt : List (Array ℕ) := survivors5 1755 titsNLevels fun a => commA a titsTArr

@[expose] def titsQt : List (Array ℕ) := titsCNt.filter inK

@[expose] def titsCCQ : List (Array ℕ) := titsCNt.filter fun c => titsQt.all fun q => commA c q

end CFSG.Sporadic.Schreier.Tits
