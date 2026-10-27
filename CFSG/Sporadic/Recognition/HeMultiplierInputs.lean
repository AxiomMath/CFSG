module

public import CFSG.LieType.Multipliers.CoverWords

public section

namespace CFSG.Sporadic.Recognition.HeMultiplier

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Sporadic.Th.Native CFSG.Sporadic.He.Native

@[expose] def invW (w : List ℤ) : List ℤ := (w.map Neg.neg).reverse

@[expose] def powW (w : List ℤ) (k : ℕ) : List ℤ := (List.replicate k w).flatten

@[expose] def xW : List ℤ := [1, 2, 2]

@[expose] def yW : List ℤ := [2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2]

@[expose] def cW : List ℤ := invW (powW xW 7) ++ powW yW 7 ++ powW xW 7

@[expose] def acW (w : List ℤ) : List ℤ := w.flatMap fun z => if z = 3 then cW else [z]

@[expose] def letterZ (l : Fin 4 × Bool) : ℤ :=
  if l.2 then (l.1.val : ℤ) + 1 else -((l.1.val : ℤ) + 1)

@[expose] def ofCodes (c : List ℕ) : List (Fin 4 × Bool) :=
  c.map fun x => (⟨x / 2 % 4, Nat.mod_lt _ (by norm_num)⟩, decide (x % 2 = 0))

@[expose] def heRelCodes : List (List ℕ) :=
  [[0, 0], [2, 2, 2], [0, 2, 0, 2, 0, 2, 0, 3, 0, 3, 0, 2, 0, 2, 0, 2, 1, 3, 1, 3, 1, 2, 1, 2, 1, 2,
   1, 3, 1, 3], [0, 2, 0, 2, 0, 3, 0, 2, 0, 2, 0, 3, 0, 2, 0, 3, 0, 2, 1, 2, 1, 3, 1, 2, 1, 2, 1, 3,
   1, 2, 1, 3], [4, 4], [0, 2, 0, 4, 0, 3, 0, 2, 0, 4, 0, 3], [0, 3, 4, 2, 0, 4, 0, 3, 4, 2, 0, 4],
   [0, 3, 4, 2, 0, 3, 4, 2, 0, 3, 4, 2, 0, 3, 4, 2], [0, 2, 4, 2, 0, 4, 3, 4, 0, 2, 5, 2, 1, 5, 3,
   5], [0, 2, 0, 3, 4, 2, 0, 2, 0, 3, 4, 2, 0, 2, 0, 3, 4, 2], [0, 2, 0, 2, 4, 3, 0, 3, 0, 3, 5, 3,
   1, 5, 1, 2, 5, 2], [0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 4, 2, 4, 3, 5, 2, 1, 3, 5, 0, 3, 0, 3, 0, 3, 0,
   3], [0, 2, 0, 3, 4, 3, 5, 2, 1, 2, 5, 1, 3, 1, 2, 1, 2, 1, 2, 1, 2, 1, 3, 4, 3], [6, 6], [0, 2,
   0, 2, 0, 2, 6, 2, 6, 2, 7, 3, 7, 0, 3, 4, 0, 3], [0, 2, 0, 2, 4, 0, 3, 4, 0, 3, 0, 6, 0, 6, 0, 7,
   1, 7, 3, 4, 3, 4], [0, 2, 0, 2, 0, 6, 2, 6, 3, 6, 3, 7, 3, 0, 3, 4, 0, 3], [0, 2, 4, 3, 0, 3, 0,
   3, 0, 6, 4, 3, 4, 0, 4, 0, 6, 0, 3, 0, 3, 4, 3], [0, 2, 0, 2, 0, 2, 4, 3, 0, 2, 4, 2, 0, 2, 0, 6,
   0, 4, 0, 4, 2, 5, 7], [0, 2, 0, 2, 0, 2, 4, 3, 0, 2, 4, 2, 0, 2, 0, 6, 0, 4, 0, 4, 2, 4, 7], [0,
   5, 3, 7, 1, 5, 3, 7, 1, 5, 3, 6], [0, 2, 0, 4, 2, 6, 0, 2, 0, 6, 0, 3, 0, 7, 4, 0, 2, 4, 0, 4, 2,
   0, 4, 3], [0, 3, 0, 6, 0, 4, 2, 4, 3, 4, 0, 7, 3, 0, 4, 3, 4, 2, 0, 4, 0, 4, 3, 0, 4]]

@[expose] def heCommCodes : Fin 4 → List (List ℕ × List ℕ)
  | 0 =>
    [([2, 0, 3], [3, 0, 3, 0, 2]), ([0, 3, 0], [3, 0, 2, 0, 2])]
  | 1 =>
    [([0, 2, 0], [3, 0, 3, 0, 2]), ([2, 0, 2, 0, 3], [0, 3, 0])]
  | 2 =>
    [([2], [4, 2, 4]), ([2, 4, 3], [4, 3, 4])]
  | 3 =>
    [([3, 4, 2], [6, 0, 2, 0]), ([6, 0, 3, 0], [3, 4, 2])]

@[expose] def uAC : List ℤ :=
  [3, 1, 3, 1, 3, 1, 3, 1, 3, 1, 3, 1, 3, 1, 3, 1, 3, 1, 3, 3, 3, 1, 3, 3, 3, 1, 3, 1, 3, 3, 3, 1,
   3, 3, 3, 1, 3, 1, 3, 3, 3, 1, 3, 1]

@[expose] def uExp : ℕ := 2

@[expose] def vAC : List ℤ :=
  [1, 3, 1, 3, 3, 1, 3, 1, 3, 3, 3, 1, 3, 3, 3, 1, 3, 1, 3, 3, 3, 1, 3, 1, 3, 1, 3, 1]

@[expose] def vExp : ℕ := 5

@[expose] def sAC : List ℤ :=
  [3, 3, 3, 1, 3, 1, 3, 3, 1, 3, 1, 3, 1, 3, 1, 3, 3, 3, 1, 3, 1, 3, 1, 3, 1, 3, 1, 3, 1, 3, 3, 1,
   3, 1, 3, 3, 3, 1, 3, 3, 3, 1]

@[expose] def sExp : ℕ := 5

@[expose] def tAB : List ℤ := [2, 1, -2]

@[expose] def surjACodes : List ℕ := [4, 6, 3, 0, 6, 4, 6, 4, 6, 0, 2, 6, 4, 3, 4, 2]

@[expose] def surjBCodes : List ℕ := [4, 2, 6, 0, 4, 0, 4, 2, 6, 0, 2, 4, 6, 2, 6, 2, 4]

@[expose] def heRels : List (List (Fin 4 × Bool)) := heRelCodes.map ofCodes

@[expose] def heComm (i : Fin 4) : List (List (Fin 4 × Bool) × List (Fin 4 × Bool)) :=
  (heCommCodes i).map fun p => (ofCodes p.1, ofCodes p.2)

@[expose] def heCommWord (i : Fin 4) : List (Fin 4 × Bool) := commWords (heComm i)

abbrev heCover : List (List (Fin 4 × Bool)) := coverWords heRels heCommWord

abbrev heRels3 := restrictWords (subsetOf _ [0, 1, 2]) heRels

abbrev heRels2 := restrictWords (subsetOf _ [0, 1]) heRels3

abbrev heCover3 := restrictWords (subsetOf _ [0, 1, 2]) heCover

abbrev heCover2 := restrictWords (subsetOf _ [0, 1]) heCover3

@[expose] def heGenWord : ℕ → List ℤ
  | 0 => powW (acW uAC) uExp
  | 1 => powW (acW vAC) vExp
  | 2 => powW (acW sAC) sExp
  | 3 => tAB
  | _ => []

@[expose] def heTabRels : List (List ℤ) :=
  (heRels ++ (List.finRange 4).map fun i => (i, false) :: heCommWord i).map (List.map letterZ)

@[expose] def heSurjA : List ℤ := (ofCodes surjACodes).map letterZ

@[expose] def heSurjB : List ℤ := (ofCodes surjBCodes).map letterZ

@[expose] def heImg (O : VOrbit) (k : ℕ) : Table := wordT 8330 (genTables O) (heGenWord k)

@[expose] def heImgLetter (T0 T1 T2 T3 V0 V1 V2 V3 : Table) (z : ℤ) : Table :=
  if z = 1 then T0 else if z = 2 then T1 else if z = 3 then T2 else if z = 4 then T3
  else if z = -1 then V0 else if z = -2 then V1 else if z = -3 then V2 else V3

@[noinline, expose] def heTabCheck : Bool :=
  let O := orbitData ()
  let T0 := heImg O 0
  let T1 := heImg O 1
  let T2 := heImg O 2
  let T3 := heImg O 3
  let V0 := invT 8330 T0
  let V1 := invT 8330 T1
  let V2 := invT 8330 T2
  let V3 := invT 8330 T3
  invOK 8330 T0 V0 && invOK 8330 T1 V1 && invOK 8330 T2 V2 && invOK 8330 T3 V3 &&
    heTabRels.all (fun r => wordT 8330 (heImgLetter T0 T1 T2 T3 V0 V1 V2 V3) r == idT 8330) &&
    wordT 8330 (heImgLetter T0 T1 T2 T3 V0 V1 V2 V3) heSurjA == O.alpha &&
    wordT 8330 (heImgLetter T0 T1 T2 T3 V0 V1 V2 V3) heSurjB == O.beta

end CFSG.Sporadic.Recognition.HeMultiplier
