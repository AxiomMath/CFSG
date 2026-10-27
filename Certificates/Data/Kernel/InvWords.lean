module

public section

namespace CFSG.KC.InvWords

@[expose] def invRedAux : List Nat → List Nat → List Nat
  | acc, [] => acc.reverse
  | [], x :: l => invRedAux [x] l
  | y :: acc, x :: l => if x == y then invRedAux acc l else invRedAux (x :: y :: acc) l

@[expose] def invRed (l : List Nat) : List Nat := invRedAux [] l

@[expose] def entryWord (R : List (List Nat)) : List Nat → List Nat
  | k :: e :: u => u ++ (if e == 1 then R.getD k [] else (R.getD k []).reverse) ++ u.reverse
  | _ => []

@[expose] def certWord (R : List (List Nat)) (c : List (List Nat)) : List Nat :=
  (c.map (entryWord R)).flatten

@[expose] def invCheck (R : List (List Nat)) (c : List (List Nat)) (t : List Nat) : Bool :=
  invRed (certWord R c) == invRed t

end CFSG.KC.InvWords
