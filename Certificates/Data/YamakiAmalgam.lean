module

public import Certificates.Data.YamakiTables

public section

namespace CFSG.ClassicalInvolution.Solomon73.Yamaki

@[expose] def sigmaWords : List (List ℕ) :=
  [[2, 6, 1, 10, 9], [6, 0, 8, 9, 10, 2, 0]]

@[expose] def tau1Words : List (List ℕ) :=
  [[0, 2, 4, 11, 8, 2, 10, 11, 8], [3, 2, 6, 8, 11, 10]]

@[expose] def tau2Words : List (List ℕ) :=
  [[7, 0, 6, 11, 8, 10, 11, 8], [1, 2, 6, 8, 1, 11, 10]]

@[expose] def r1Words : List (List ℕ) :=
  [[0], [1, 1, 1, 0, 1, 1, 0, 1, 0, 1]]

@[expose] def repWords : List (List ℕ × List ℕ) :=
  [([0], [1]), ([0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0], [0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0]),
    ([0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0], [0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 1]),
    ([0], [0, 0, 1, 0, 0, 1, 0, 1, 1, 1, 0, 1, 1]), ([0, 1, 1, 1], [0, 0, 0, 0, 1]),
    ([1, 0, 1, 1, 0, 1, 1, 1, 1, 0], [0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0]),
    ([1, 0, 1, 1, 0, 1, 1, 1, 1, 0], [0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 1]),
    ([0, 1, 1, 1], [0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1]),
    ([1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1], [0, 0, 1, 0, 0, 1, 0, 1, 1, 1, 0, 1, 1]),
    ([0, 0, 0, 0, 1, 1, 1, 0, 1, 1, 1], [0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1]),
    ([0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1], [0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1]),
    ([0, 1, 0, 0, 1, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1, 0, 1, 1]),
    ([0], [0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0]),
    ([0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 0, 0, 1, 1, 1]),
    ([0, 1, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0], [0, 1, 0, 1, 1]),
    ([0, 1, 0, 1, 1, 0, 1, 1], [0, 0, 1, 0, 1, 0, 1])]

@[expose] def tests1 : List (List ℕ) :=
  [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0]]

@[expose] def tests2 : List (List ℕ) :=
  [[0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1], [0, 0, 1, 1, 1, 0, 0, 1, 1, 1],
    [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1],
    [0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0,
     0, 1]]

@[expose] def chainData : List (List ℕ × List (Bool × List ℕ × List ℕ)) :=
  [([0, 0, 0, 0],
    [(false, [10, 9], [0, 0, 1, 0, 0, 1, 0, 0, 1]),
      (true, [5, 8, 11, 10, 2], [0, 1, 0, 1, 1, 0, 0, 0, 0, 0]),
      (false, [0, 3, 2, 9, 0, 10, 9, 0], [1, 1, 0, 1, 0, 1, 1, 1, 0]),
      (true, [2, 10, 11, 10, 2], [1, 0, 1, 0]),
      (false, [2, 9, 10, 9], [0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1])]),
   ([0, 0, 0, 0],
    [(false, [10, 2, 9], [0, 0, 0, 1, 1, 1, 0]),
      (true, [5, 8, 11, 10, 2], [0, 0, 0, 1, 0, 1, 0, 0, 1, 0]),
      (false, [1, 3, 10, 9, 0, 2, 10, 9], [1, 1, 0, 1, 0, 1, 1, 1, 0]),
      (true, [2, 10, 11, 10, 2], [1, 0, 1, 0]),
      (false, [1, 2, 9, 10, 9], [0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1])]),
   ([0, 0, 0, 0],
    [(false, [10, 9], [0, 0, 1, 0, 0, 1, 0, 0, 1]),
      (true, [5, 8, 11, 10, 2], [0, 1, 0, 1, 1, 0, 0, 0, 0, 0]),
      (false, [0, 2, 9, 0, 10, 9, 0], [1, 1, 0, 1, 0, 1, 1, 1, 0]),
      (true, [2, 10, 11, 10, 2], [1, 0, 1, 0]),
      (false, [2, 0, 9, 10, 9], [0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1])]),
   ([0, 0, 0, 0],
    [(false, [2, 9], [0, 0, 1, 0, 0, 1, 0, 0, 1]),
      (true, [5, 8, 11, 10, 2], [0, 1, 0, 1, 1, 0, 0, 0, 0, 0]),
      (false, [0, 9, 0], [1, 1, 0, 1, 0, 1, 1, 1, 0]), (true, [2, 10, 11, 10, 2], [1, 0, 1, 0]),
      (false, [9], [0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1])]),
   ([0, 0, 0, 0],
    [(false, [10, 2, 9], [0, 0, 0, 1, 1, 1, 0]),
      (true, [5, 8, 11, 10, 2], [0, 0, 0, 1, 0, 1, 0, 0, 1, 0]),
      (false, [1, 10, 9, 0, 2, 10, 9], [1, 1, 0, 1, 0, 1, 1, 1, 0]),
      (true, [2, 10, 11, 10, 2], [1, 0, 1, 0]),
      (false, [0, 2, 9, 10, 9], [0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1])]),
   ([0, 0, 0, 0],
    [(false, [2, 9, 0], [0, 0, 0, 1, 1, 1, 0]),
      (true, [5, 8, 11, 10, 2], [0, 0, 0, 1, 0, 1, 0, 0, 1, 0]),
      (false, [9], [1, 1, 0, 1, 0, 1, 1, 1, 0]), (true, [2, 10, 11, 10, 2], [1, 0, 1, 0]),
      (false, [0, 9], [0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1])]),
   ([0, 0, 0, 0],
    [(false, [2, 9], [0, 0, 1, 0, 0, 1, 0, 0, 1]),
      (true, [5, 8, 11, 10, 2], [0, 1, 0, 1, 1, 0, 0, 0, 0, 0]),
      (false, [0, 4, 6, 9, 0], [1, 1, 0, 1, 0, 1, 1, 1, 0]),
      (true, [2, 10, 11, 10, 2], [1, 0, 1, 0]),
      (false, [1, 9], [0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1])]),
   ([0, 0, 0, 0],
    [(false, [2, 9, 0], [0, 0, 0, 1, 1, 1, 0]),
      (true, [5, 8, 11, 10, 2], [0, 0, 0, 1, 0, 1, 0, 0, 1, 0]),
      (false, [4, 6, 9], [1, 1, 0, 1, 0, 1, 1, 1, 0]), (true, [2, 10, 11, 10, 2], [1, 0, 1, 0]),
      (false, [2, 0, 9], [0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1])])]

@[expose] def sigmaA (_ : Unit := ()) : Array (Array ℕ) := wordsA (genA ()) sigmaWords

@[expose] def tau1A (_ : Unit := ()) : Array (Array ℕ) := wordsA (genA ()) tau1Words

@[expose] def tau2A (_ : Unit := ()) : Array (Array ℕ) := wordsA (genA ()) tau2Words

@[expose] def tabS (_ : Unit := ()) : Array (Array ℕ) := buildF (enumN ()) (sigmaA ())

@[expose] def tabT1 (_ : Unit := ()) : Array (Array ℕ) := buildF (enumH ()) (tau1A ())

@[expose] def tabT2 (_ : Unit := ()) : Array (Array ℕ) := buildF (enumH ()) (tau2A ())

@[expose] def r1A (_ : Unit := ()) : Array (Array ℕ) := wordsA (gX ()) r1Words

@[expose] def repsA (_ : Unit := ()) : Array (Array ℕ × Array ℕ) :=
  let g := gX ()
  (repWords.map fun p => (wordA g p.1, wordA g p.2)).toArray

@[expose] def crGenCheck (_ : Unit := ()) : Bool :=
  wordsIn idxN0 sigmaWords && wordsIn idxHhat tau1Words && wordsIn idxHhat tau2Words

@[expose] def autCheck (_ : Unit := ()) : Bool :=
  let EN := enumN ()
  let EH := enumH ()
  autOK EN (gN ()) (sigmaA ()) (tabS ()) && autOK EH (gH ()) (tau1A ()) (tabT1 ()) &&
    autOK EH (gH ()) (tau2A ()) (tabT2 ())

@[expose] def stabCheck (_ : Unit := ()) : Bool :=
  let EX := enumX ()
  let EN := enumN ()
  let EH := enumH ()
  let S := tabS ()
  let T1 := tabT1 ()
  let T2 := tabT2 ()
  let g := gX ()
  let a := (genA ())[5]!
  (allLt 2 fun j => (EX.lookup (appF EN S g[j]!)).isSome &&
    (EX.lookup (appF EH T1 g[j]!)).isSome && (EX.lookup (appF EH T2 g[j]!)).isSome) &&
    decide (appF EH T1 a = a) && decide (appF EH T2 a = a)

@[expose] def stdRep (EN EH : Enum) (S T1 T2 : Array (Array ℕ)) (k : ℕ) (t : Array ℕ) :
    Array ℕ :=
  let t := if k % 2 = 1 then appF EH T2 t else t
  let t := if k / 2 % 2 = 1 then appF EH T1 t else t
  if k / 4 % 2 = 1 then appF EN S t else t

@[expose] def stdCheck (_ : Unit := ()) : Bool :=
  let EN := enumN ()
  let EH := enumH ()
  let S := tabS ()
  let T1 := tabT1 ()
  let T2 := tabT2 ()
  let g := gX ()
  let P := repsA ()
  decide (P.size = 16) && allLt 8 fun k =>
    decide (P[k]!.1 = stdRep EN EH S T1 T2 k g[0]!) &&
      decide (P[k]!.2 = stdRep EN EH S T1 T2 k g[1]!)

@[expose] def invA (t : Array ℕ) : Array ℕ := Id.run do
  let mut r := Array.replicate 64 0
  for i in [0:64] do
    r := r.set! t[i]! i
  return r

@[expose] def conjIndex1 (E : Enum) (R : Array (Array ℕ)) : Std.HashMap (Array ℕ) (ℕ × ℕ) :=
  (List.range R.size).foldl (init := {}) fun m r => (List.range E.elems.size).foldl (init := m)
    fun m j => let x := E.elems[j]!
      let t := compA (compA (invA x) R[r]!) x
      if m.contains t then m else m.insert t (r, j)

@[expose] def conjIndex2 (E : Enum) (P : Array (Array ℕ × Array ℕ)) :
    Std.HashMap (Array ℕ × Array ℕ) (ℕ × ℕ) :=
  (List.range P.size).foldl (init := {}) fun m k => (List.range E.elems.size).foldl (init := m)
    fun m j => let x := E.elems[j]!
      let xi := invA x
      let t := (compA (compA xi P[k]!.1) x, compA (compA xi P[k]!.2) x)
      if m.contains t then m else m.insert t (k, j)

@[expose] def pattOK (ys : Array (Array ℕ)) (tests : List (List ℕ)) (ex : List Bool) : Bool :=
  (tests.zip ex).all fun p => decide (wordA ys p.1 = idA ()) == p.2

@[expose] def c1Check (_ : Unit := ()) : Bool :=
  let E := enumX ()
  let R := r1A ()
  let g := gX ()
  let ex := tests1.map fun w => decide (wordA #[g[0]!] w = idA ())
  let m := conjIndex1 E R
  allLt E.elems.size fun i =>
    let y := E.elems[i]!
    !(pattOK #[y] tests1 ex) ||
      match m[y]? with
      | some (r, j) => decide (r < R.size) && decide (j < E.elems.size) &&
          decide (compA E.elems[j]! y = compA R[r]! E.elems[j]!)
      | none => false

@[expose] def c2Check (_ : Unit := ()) : Bool :=
  let E := enumX ()
  let R := r1A ()
  let g := gX ()
  let P := repsA ()
  let ex := tests2.map fun w => decide (wordA g w = idA ())
  let m := conjIndex2 E P
  allLt R.size fun r => allLt E.elems.size fun i =>
    let c := R[r]!
    let y := E.elems[i]!
    !(pattOK #[c, y] tests2 ex) ||
      match m[(c, y)]? with
      | some (k, j) => decide (k < P.size) && decide (j < E.elems.size) &&
          decide (compA E.elems[j]! c = compA P[k]!.1 E.elems[j]!) &&
          decide (compA E.elems[j]! y = compA P[k]!.2 E.elems[j]!)
      | none => false

@[expose] def stepsOK (G g ys : Array (Array ℕ)) :
    List ℕ → List (Bool × List ℕ × List ℕ) → Bool
  | cur, [] => decide (wordA g cur = compA G[5]! G[4]!)
  | cur, (kind, w, nxt) :: rest =>
    (if kind then wordsIn idxHhat [w] &&
        decide (compA (wordA G w) (wordA g nxt) = compA (wordA g cur) (wordA G w))
      else wordsIn idxN0 [w] &&
        decide (compA (wordA G w) (wordA ys nxt) = compA (wordA ys cur) (wordA G w))) &&
      stepsOK G g ys nxt rest

@[expose] def chainCheck (_ : Unit := ()) : Bool :=
  let G := genA ()
  let g := gX ()
  let P := repsA ()
  decide (chainData.length = 8) && allLt 8 fun k =>
    let ch := chainData[k]!
    let ys := #[P[8 + k]!.1, P[8 + k]!.2]
    decide (wordA g ch.1 = G[4]!) && stepsOK G g ys ch.1 ch.2

end CFSG.ClassicalInvolution.Solomon73.Yamaki
