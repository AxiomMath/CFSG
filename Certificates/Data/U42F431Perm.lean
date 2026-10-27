module

public section

namespace U42F431

abbrev PL := List Nat

@[expose] def idL : PL := List.range 45

@[expose] def comp (l m : PL) : PL := m.map fun j => l.getD j 0

@[expose] def xL : PL :=
  [0, 2, 1, 6, 7, 8, 3, 4, 5, 12, 13, 14, 9, 10, 11, 15, 16, 19, 22, 17, 20, 23, 18, 21, 24, 25,
    26, 29, 32, 27, 30, 33, 28, 31, 34, 35, 36, 39, 42, 37, 40, 43, 38, 41, 44]

@[expose] def yL : PL :=
  [38, 0, 42, 18, 32, 13, 28, 10, 22, 8, 33, 17, 31, 19, 5, 34, 11, 25, 4, 23, 7, 30, 26, 14, 21,
    35, 39, 44, 1, 41, 2, 36, 40, 37, 43, 16, 27, 20, 6, 9, 3, 15, 24, 29, 12]

@[expose] def yiL : PL :=
  (List.range 45).map fun i => ((List.range 45).find? fun j => yL.getD j 0 == i).getD 0

@[expose] def genL (k : Nat) : PL := if k % 3 = 0 then xL else if k % 3 = 1 then yL else yiL

@[expose] def evalW (w : List Nat) : PL := w.foldr (fun k acc => comp (genL k) acc) idL

@[expose] def invLet (k : Nat) : Nat := if k % 3 = 1 then 2 else if k % 3 = 2 then 1 else 0

@[expose] def invW (w : List Nat) : List Nat := (w.map invLet).reverse

@[expose] def applyW (w : List Nat) (p : Nat) : Nat := w.foldr (fun k acc => (genL k).getD acc 0) p

end U42F431
