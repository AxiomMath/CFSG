module

public import Certificates.Data.CFSGNative.LyFive.Conj
public import CFSG.RankThree.Native.LyFiveCheckInputs

public section

namespace CFSG.RankThree.PartOne.LyFive

open CFSG.Sporadic.Ly.Native CFSG.Sporadic.LySchreier CFSG.Sporadic.LySchreier.Native
  CFSG.Sporadic.He.Native CFSG.Sporadic.Th.Native CFSG.RankThree.Native

@[expose] def lyFiveYArr : Array (Array ℕ) := mulM 5 111 lyFiveVArr[0]! lyFiveVArr[1]!

@[expose] def classB4 : Mat := powM 5 111 matB 4

@[expose] def classHp : Array (Array ℕ × Array ℕ) := hGenPairs (aStarArr classB4)

@[expose] def classT (τ : List ℤ) : Mat := evalWordM seedM (seedMInv classB4) τ

@[expose] def classR (w : Mat) (τ : List ℤ) : Array ℕ :=
  restrArr (mulM 5 111 (mulM 5 111 (invM 5 111 (classT τ)) w) (classT τ))

@[expose] def classTree (w : Mat) (τ : List ℤ) (N : ℕ) :
    Array (Array ℕ) × Array ℕ × Array ℕ :=
  conjBFS (classR w τ) classHp N

@[expose] def classOK (w : Mat) (τ : List ℤ) (N : ℕ) (closed : Bool) : Bool :=
  mulM 5 111 (classT τ) (invM 5 111 (classT τ)) == idM 111 &&
    conjTreeOK (classR w τ) classHp (classTree w τ N) && decide (0 < N) &&
    decide (N ≤ (classTree w τ N).1.size) &&
    (!closed || (conjClosedOK classHp (classTree w τ N) && (classTree w τ N).1.size == N))

@[expose] def lyXClassOK : Bool := classOK lyFiveXArr xWord 390600 false

@[expose] def lyY3ClassOK : Bool := classOK lyFiveYArr y3Word 1562400 true

@[expose] def lyY1ClassOK : Bool := classOK lyFiveYArr y1Word 4687200 false

@[expose] def dLifts : List (List ℤ × ℕ × List ℕ) := [
    ([], 0, [0, 0, 0, 0]),
    ([2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1], 0, [0, 0, 0, 3]),
    ([2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1], 0, [0, 0, 0, 4]),
    ([2, 2, 1, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1], 0, [0, 0, 0, 1]),
    ([2, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1], 0, [0, 0, 0, 3]),
    ([2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2], 0, [0, 0, 0, 0])]

@[expose] def uVecs : List (List ℕ) := [[0, 0, 1, 0], [0, 1, 0, 3]]

@[expose] def nfArr (c : ℕ) (e : List ℕ) : Array (Array ℕ) :=
  fiveNFDirect (c % 5) fun j => e.getD j.val 0 % 5

@[expose] def lyYCommOK : Bool :=
  (dLifts.all fun d =>
    let D := mulM 5 111 (fiveWordArr d.1) (nfArr d.2.1 d.2.2)
    mulM 5 111 D lyFiveYArr == mulM 5 111 lyFiveYArr D) &&
  (uVecs.all fun u =>
    let F := nfArr 0 u
    mulM 5 111 F lyFiveYArr == mulM 5 111 lyFiveYArr F)

end CFSG.RankThree.PartOne.LyFive
