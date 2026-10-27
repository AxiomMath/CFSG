module

public import Init

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabMThreeA

@[expose] def kmLetter (u : Nat) : Nat :=
  match u with
  | 0 => 3
  | 1 => 2
  | 2 => 1
  | 3 => 0
  | 4 => 10
  | 5 => 4
  | 6 => 5
  | 7 => 6
  | 8 => 9
  | 9 => 7
  | 10 => 8
  | _ => 0

@[expose] def kmOfY (w : List Nat) : List Nat := w.map kmLetter

@[expose] def kmSchreier : List Nat → List (Nat × Bool)
  | x :: y :: w =>
    ((if x = 0 then [] else [(x - 1, false)]) ++ (if y = 0 then [] else [(y - 1, true)])) ++
      kmSchreier w
  | _ => []

@[expose] def kmSpider : List Nat := (List.replicate 10 [3, 2, 1, 3, 4, 5, 3, 7, 8]).flatten

@[expose] def kmF0L : List Nat := (List.replicate 9 [3, 2, 1, 0, 4, 5, 7]).flatten ++ [11]

@[expose] def yW23 : List Nat :=
  [2, 5, 6, 1, 3, 0, 5, 8, 5, 10, 8, 7, 8, 2, 3, 2, 3, 1, 0, 9, 7, 1, 3, 6, 9, 7, 2, 5, 3, 6, 7,
    2, 1, 9, 6, 0, 8, 9, 10, 5, 0, 5, 6, 5, 0, 9, 3, 0, 8, 10, 6, 7, 9, 7, 1, 9, 10, 3, 6, 2, 9,
    7, 8, 7, 2, 3, 2, 3, 2, 9, 10, 9, 10, 6, 7, 6, 1, 2, 9, 5, 0, 5, 7, 0, 9, 1, 0, 10, 0, 5, 6,
    8, 3, 9, 2, 7, 3, 0, 1, 10, 5, 0, 1, 0, 2, 9, 3, 8, 6, 3, 7, 8, 0, 3, 10, 7, 8, 3, 2, 9, 7,
    6, 10, 5, 2, 0, 7, 1, 3, 2, 1, 5, 6, 2, 3, 8, 0, 9, 8, 5, 1, 6, 2, 1, 5, 0, 3, 10, 3, 2]

@[expose] def kmRelWords (_ : Unit := ()) : List (List Nat) :=
  [kmSpider, kmF0L, (List.replicate 23 (kmOfY yW23)).flatten]

@[expose] def kmRels (_ : Unit := ()) : List (List (Nat × Bool)) := (kmRelWords ()).map kmSchreier

@[expose] def yMoves : List (List Nat) :=
  [yW23, [2, 6], [2, 8], [2, 10], [6, 8], [6, 10], [8, 10], [2, 6, 8, 10]]

@[expose] def kmMoves (_ : Unit := ()) : List (List (Nat × Bool)) :=
  yMoves.map fun w => kmSchreier (kmOfY w)

end CFSG.HardMathSupport.Dickson.I271.TabMThreeA
