module

public import Certificates.Data.CFSGNative.Co2Smith.Check

public section

namespace CFSG.Sporadic.Co2Smith.Native

open CFSG.Sporadic.SmallF2.Native

@[expose] def sp6GenMix : List (List Nat) :=
  [[2, 3, 3, 3, 3, 3, 3, 2, 3, 2, 2, 3, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2,
    2, 3, 2, 2, 3, 3, 3, 3, 3, 3], [2, 2, 3, 3, 2, 2, 3, 3, 2, 2, 3, 3, 3, 3, 3, 3, 2, 2, 3, 3, 3,
    3, 3, 3, 2, 3, 3, 3, 3, 3, 3, 2, 2, 3, 2], [3, 2, 3, 3, 3, 3, 3, 3, 2, 2, 3, 3, 3, 3, 3, 3, 2,
    3, 3, 3, 3, 3, 3, 2, 2, 3, 2, 2, 3, 3, 3, 3, 3, 3, 2, 2, 3, 2, 2, 3], [2, 3, 3, 3, 2, 3, 2, 3,
    3, 3, 3, 3, 3, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 3, 2, 3, 2], [3, 3, 2, 2, 3, 3, 3,
    3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
    3, 3, 2, 3, 3, 3, 2, 2, 3], [2, 2, 3, 3, 2, 2, 3, 2, 2, 3, 3, 3, 3, 3, 3, 2, 3, 3, 3, 3, 3, 3,
    2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 3, 3, 3, 3, 3, 3], [2, 3, 3, 3, 2,
    3, 2, 3, 3, 3, 3, 3, 3, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 3, 2, 3, 2, 2, 2, 3, 3, 2,
    2, 3, 3, 2, 2, 3, 3, 3, 3, 3, 3, 2, 2, 3, 3, 3, 3, 3, 3, 2, 3, 3, 3, 3, 3, 3, 2, 2, 3, 2, 2, 2,
    3, 3, 2, 2, 3, 2, 2, 3, 3, 3, 3, 3, 3, 2, 3, 3, 3, 3, 3, 3, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
    3, 3, 3, 3, 3, 3, 3, 2, 3, 3, 3, 3, 3, 3], [2, 3, 3, 3, 3, 3, 3, 2, 3, 2, 2, 3, 2, 3, 3, 3, 3,
    3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 2, 3, 2, 2, 3, 3, 3, 3, 3, 3, 3, 2, 3, 3, 3, 3, 3,
    3, 2, 2, 3, 3, 3, 3, 3, 3, 2, 3, 3, 3, 3, 3, 3, 2, 2, 3, 2, 2, 3, 3, 3, 3, 3, 3, 2, 2, 3, 2, 2,
    3, 2, 2, 3, 3, 2, 2, 3, 2, 2, 3, 3, 3, 3, 3, 3, 2, 3, 3, 3, 3, 3, 3, 2, 3, 3, 3, 3, 3, 3, 3, 3,
    3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 3, 3, 3, 3, 3, 3, 3, 3, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
    3, 3, 3, 3, 3, 3, 3, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 3, 3, 3, 2, 2,
    3]]

@[expose] def sp6Rels (_ : Unit := ()) : List (List (Fin 8 × Bool)) :=
  [[(0, true), (0, true)], [(1, true), (1, true)], [(2, true), (2, true)], [(3, true), (3, true)],
    [(4, true), (4, true)], [(5, true), (5, true), (5, true)], [(0, true), (1, false), (0, true),
    (1, false)], [(0, true), (2, false), (0, true), (2, false), (0, true), (2, false)], [(0, true),
    (3, false), (0, true), (3, false)], [(0, true), (4, false), (0, true), (4, false)], [(0, true),
    (5, false), (0, true), (5, false)], [(1, true), (2, false), (1, true), (2, false)], [(1, true),
    (3, false), (1, true), (3, false), (1, true), (3, false)], [(1, true), (4, false), (1, true),
    (4, false)], [(1, true), (5, false), (1, true), (5, false)], [(2, true), (3, false), (2, true),
    (3, false), (2, true), (3, false)], [(2, true), (4, false), (2, true), (4, false)], [(2, true),
    (5, false), (2, true), (5, false)], [(3, true), (4, false), (3, true), (4, false), (3, true),
    (4, false)], [(3, true), (5, false), (3, true), (5, false)], [(4, true), (5, false), (4, true),
    (5, false), (4, true), (5, false)], [(6, false), (3, true), (1, true), (5, true)], [(7, false),
    (0, true), (2, true), (5, true), (4, true)], [(6, true), (6, true), (6, true)], [(7, true),
    (7, true), (7, true)], [(6, true), (7, true), (6, true), (7, true), (6, true), (7, true),
    (6, true), (7, true), (6, true), (7, true), (6, true), (7, true), (6, true), (7, true),
    (6, true), (7, true), (6, true), (7, true), (6, true), (7, true), (6, true), (7, true),
    (6, true), (7, true)], [(6, true), (7, false), (6, true), (7, false), (6, true), (7, false),
    (6, true), (7, false), (6, true), (7, false), (6, true), (7, false), (6, true), (7, false),
    (6, true), (7, false)], [(6, true), (7, true), (6, false), (7, true), (6, true), (7, true),
    (6, false), (7, true), (6, true), (7, false), (6, false), (7, false)]]

@[expose] def sp6Pairs : Fin 8 → List (List (Fin 8 × Bool) × List (Fin 8 × Bool))
  | 0 =>
    [([(0, true), (3, true), (2, true), (4, true), (5, true), (4, true)],
      [(0, true), (2, true), (3, true), (2, true), (5, false), (4, true)])]
  | 1 =>
    [([(4, true), (3, true), (1, true), (5, true)],
      [(0, true), (3, true), (4, true), (5, true), (4, true)])]
  | 2 =>
    [([(4, true), (3, true), (5, false)],
      [(3, true), (5, true), (4, true), (3, true), (2, true), (0, true)])]
  | 3 =>
    [([(2, true), (5, false), (4, true), (5, true)],
      [(4, true), (3, true), (2, true), (5, false), (4, true), (3, true), (1, true), (5, true)])]
  | 4 =>
    [([(2, true), (5, false), (4, true), (5, true)],
      [(1, true)])]
  | 5 =>
    [([(0, true), (1, true), (2, true), (5, false)],
      [(5, true)])]
  | 6 =>
    [([(6, false)],
      [(7, true), (6, true), (7, false), (6, true), (7, true), (6, false), (7, false), (6, false),
        (7, true)])]
  | 7 =>
    [([(7, false)],
      [(6, true), (7, false), (6, false), (7, false), (6, true)])]

@[expose] def sp6Wa (_ : Unit := ()) : List (Fin 8 × Bool) :=
  [(0, true), (2, true), (3, true), (5, true), (4, true), (3, true), (1, true), (2, true),
    (0, true), (3, true), (2, true), (4, true), (3, true), (1, true), (5, true), (4, true),
    (3, true), (1, true), (2, true), (0, true), (5, false), (4, true), (5, true)]

@[expose] def sp6Wb (_ : Unit := ()) : List (Fin 8 × Bool) :=
  [(3, true), (1, true), (4, true), (3, true), (2, true), (0, true), (5, true), (4, true),
    (3, true), (1, true), (2, true), (5, true), (4, true), (3, true), (1, true), (2, true),
    (5, true), (4, true), (3, true), (1, true), (2, true), (0, true), (5, false), (4, true),
    (3, true), (1, true), (2, true), (0, true), (3, true), (4, true), (5, true), (4, true)]

@[expose] def invRevN {m : Nat} (w : List (Fin m × Bool)) : List (Fin m × Bool) :=
  (w.map fun l => (l.1, !l.2)).reverse

@[expose] def commWordN {m : Nat} (u v : List (Fin m × Bool)) : List (Fin m × Bool) :=
  u ++ v ++ invRevN u ++ invRevN v

@[expose] def commWordsN {m : Nat} (c : List (List (Fin m × Bool) × List (Fin m × Bool))) :
    List (Fin m × Bool) :=
  (c.map fun p => commWordN p.1 p.2).flatten

@[expose] def coverWordsN {m : Nat} (R : List (List (Fin m × Bool)))
    (w : Fin m → List (Fin m × Bool)) : List (List (Fin m × Bool)) :=
  (List.finRange m).flatMap (fun i => R.map fun r => commWordN [(i, true)] r) ++
    (List.finRange m).map fun i => (i, false) :: w i

@[expose] def sp6CoverR (_ : Unit := ()) : List (List (Fin 8 × Bool)) :=
  coverWordsN sp6Rels fun i => commWordsN (sp6Pairs i)

@[expose] def sCode {m : Nat} (l : Fin m × Bool) : Nat :=
  if l.2 then 2 * l.1.val else 2 * l.1.val + 1

@[expose] def invMix (w : List Nat) : List Nat :=
  w.reverse.flatMap fun l => if l == 2 then [2, 2] else [3, 3, 3, 3, 3, 3]

@[expose] def sp6LetterMix (k : Nat) : List Nat :=
  if k % 2 == 0 then sp6GenMix[k / 2]! else invMix sp6GenMix[k / 2]!

@[expose] def sp6LetterRows (seeds : Array (Array Nat)) : Array (Array Nat) :=
  (Array.range 16).map fun k => mRows seeds (sp6LetterMix k)

@[expose] def sp6Check (seeds : Array (Array Nat)) : Bool :=
  let L := sp6LetterRows seeds
  (List.range 8).all (fun i => wRows L [2 * i, 2 * i + 1] == idRows 22) &&
    sp6Rels.all (fun r => wRows L (r.map sCode) == idRows 22) &&
    (List.finRange 8).all (fun i =>
      wRows L ((commWordsN (sp6Pairs i)).map sCode) == wRows L [2 * i.val]) &&
    wRows L (sp6Wa.map sCode) == mRows seeds [2] &&
    wRows L (sp6Wb.map sCode) == mRows seeds [3]

end CFSG.Sporadic.Co2Smith.Native
