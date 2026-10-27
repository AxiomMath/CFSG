module

public import Certificates.Data.TitsAschbacherParrott
public import CFSG.Sporadic.Schreier.TitsInvCheckInputs
public import CFSG.Quasithin.Recognition.RuRank3TitsClsInputs

public section

namespace Certificates.TitsAschbacherSecFour

open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2.Native Certificates.TitsAschbacherParrott

@[expose] def nArr (w : List ℕ) : Array ℕ := prodArr titsNArrs w

@[expose] def nLetters (w : List ℕ) : Bool := w.all fun l => decide (l < 4)

@[expose] def commWordA : List ℕ := [0, 0, 1, 2]

@[expose] def commWordB : List ℕ := [1, 0, 2, 3, 3]

@[expose] def tCommCheck : Bool :=
  nLetters commWordA && nLetters commWordB &&
    commA (nArr commWordA) titsTArr && commA (nArr commWordB) titsTArr &&
    eqA 1755 (compA 1755 (nArr commWordA) (nArr commWordB))
      (compA 1755 (compA 1755 titsTArr (nArr commWordB)) (nArr commWordA))

@[expose] def u1Word : List ℕ := [0, 0, 0, 0]

@[expose] def u2Word : List ℕ := [0, 3, 0, 3]

@[expose] def yWord : List ℕ := [3, 2]

@[expose] def eWord : List ℕ := [3]

@[expose] def fWords : List (List ℕ) := [[0], [0, 1], [1]]

@[expose] def qWords : List (List ℕ) :=
  [[2, 3, 3, 0, 2, 1], [0, 2, 1, 3, 0, 3, 2], [2, 0, 1, 1, 2, 3, 3]]

@[expose] def u1A : Array ℕ := nArr u1Word

@[expose] def u2A : Array ℕ := nArr u2Word

@[expose] def u3A : Array ℕ := compA 1755 u1A u2A

@[expose] def uSharp : List (Array ℕ) := [u1A, u2A, u3A]

@[expose] def yA : Array ℕ := nArr yWord

@[expose] def eA : Array ℕ := nArr eWord

@[expose] def qArrs : List (Array ℕ) := qWords.map nArr

@[expose] def u10List : List (Array ℕ) :=
  [idA 1755, u1A, u2A, u3A, titsTArr, compA 1755 titsTArr u1A, compA 1755 titsTArr u2A,
    compA 1755 titsTArr u3A]

@[expose] def structCheck : Bool :=
  nLetters u1Word && nLetters u2Word && nLetters yWord && nLetters eWord &&
    fWords.all nLetters && qWords.all nLetters &&
    eqA 1755 (compA 1755 u1A u1A) (idA 1755) && eqA 1755 (compA 1755 u2A u2A) (idA 1755) &&
    commA u1A u2A && !eqA 1755 u1A (idA 1755) && !eqA 1755 u2A (idA 1755) &&
    !eqA 1755 u1A u2A && commA u1A titsTArr && commA u2A titsTArr && commA yA titsTArr &&
    eqA 1755 (compA 1755 yA u1A) (compA 1755 u2A yA) &&
    eqA 1755 (compA 1755 yA u2A) (compA 1755 u3A yA) &&
    eqA 1755 (powA yA 3) (idA 1755) && !eqA 1755 yA (idA 1755) &&
    eqA 1755 (compA 1755 eA titsZArr) (compA 1755 u1A eA) &&
    (fWords.zip uSharp).all (fun p => eqA 1755 (compA 1755 (nArr p.1) titsTArr)
      (compA 1755 (compA 1755 p.2 titsTArr) (nArr p.1))) &&
    qArrs.all (fun q => commA q titsTArr && commA q u1A && commA q u2A)

@[expose] def sqIter : ℕ → Array ℕ → Array ℕ
  | 0, c => c
  | k + 1, c => sqIter k (compA 1755 c c)

@[expose] def cOK (c : Array ℕ) : Bool :=
  uSharp.any (fun u => eqA 1755 (compA 1755 c u1A) (compA 1755 u c)) &&
    uSharp.any (fun u => eqA 1755 (compA 1755 c u2A) (compA 1755 u c)) &&
    (!(qArrs.all fun q => commA c q) || u10List.any (eqA 1755 c)) &&
    (!(commA c u1A && commA c u2A) || eqA 1755 (sqIter 10 c) (idA 1755))

@[expose] def enumCheck : Bool :=
  titsCNt.all fun c => cOK c && cOK (compA 1755 CFSG.Quasithin.RuRank3.titsAuxArr c)

end Certificates.TitsAschbacherSecFour
