module

public import Certificates.Data.K426Checks
public import CFSG.Sporadic.Schreier.PairJ3CheckInputs

public section

namespace CFSG.RankThree.PartTwo.KFacts.K426

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu
  CFSG.Monster.B.Fischer CFSG.RankThree.Native
  CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest

@[expose] def j3tHex : String := include_str "K426J3.txt"

@[expose] def j3tArr (k : ℕ) : Array ℕ := hexTable 4 6156 (6156 * k) j3tHex

@[expose] def j3tCBGens : Array (Array ℕ) := Array.ofFn fun j : Fin 5 => j3tArr (0 + j.val)

@[expose] def j3tLines : Array (Array ℕ) := Array.ofFn fun j : Fin 13 => j3tArr (5 + j.val)

@[expose] def j3tReps : Array (Array ℕ) := Array.ofFn fun j : Fin 2 => j3tArr (18 + j.val)

@[expose] def j3tTrans : Array (Array ℕ) := Array.ofFn fun j : Fin 13 => j3tArr (20 + j.val)

@[expose] def j3tRec : List ℕ :=
  [0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1]

@[expose] def j3tRelsA : List (ℕ × ℕ × ℕ) :=
  [(0, 1, 1), (1, 2, 1), (2, 0, 1)]

@[expose] def j3tRelsB : List (ℕ × ℕ × ℕ) :=
  [(0, 1, 1), (1, 2, 1), (2, 0, 1)]

@[expose] def j3tCAGens : Array (Array ℕ) := Array.ofFn fun j : Fin 4 => j3tArr (33 + j.val)

@[expose] def j3tDGens : Array (Array ℕ) := Array.ofFn fun j : Fin 2 => j3tArr (37 + j.val)

@[expose] def j3tG : Array ℕ := j3tArr 39

@[expose] def j3tWu : List (Fin 2 × Bool) :=
  [(0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true),
    (1, false), (0, true), (1, true), (0, true)]

@[expose] def j3tWv : List (Fin 2 × Bool) :=
  [(1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true)]

@[expose] def wordPow {m : ℕ} (w : List (Fin m × Bool)) (k : ℕ) : List (Fin m × Bool) :=
  (List.replicate k w).flatten

@[expose] def j3tAB : List (Fin 2 × Bool) := [(0, true), (1, true)]

@[expose] def j3tABB : List (Fin 2 × Bool) := [(0, true), (1, true), (1, true)]

@[expose] def j3tA6Rels : List (List (Fin 2 × Bool)) :=
  [wordPow [(0, true)] 2, wordPow [(1, true)] 4, wordPow j3tAB 5, wordPow j3tABB 5]

@[expose] def j3tLiftRels : List (List (Fin 2 × Bool)) :=
  [wordPow [(0, true)] 2, wordPow [(1, true)] 4, wordPow j3tAB 15, wordPow j3tABB 15,
    commW (wordPow j3tAB 5) [(0, true)], commW (wordPow j3tAB 5) [(1, true)],
    commW (wordPow j3tABB 5) [(0, true)], commW (wordPow j3tABB 5) [(1, true)],
    commW j3tWu j3tWv]

@[expose] def j3tKeys : List ℕ := [0, 1, 3, 2]

@[expose] def j3tCBCert : ArrCert := enumBfs 6156 j3tCBGens j3tKeys 300

@[expose] def j3tCACert : ArrCert := enumBfs 6156 j3tCAGens j3tKeys 1200

@[expose] def j3tDCert : ArrCert := enumBfs 6156 j3tDGens j3tKeys 400

end CFSG.RankThree.PartTwo.KFacts.K426
