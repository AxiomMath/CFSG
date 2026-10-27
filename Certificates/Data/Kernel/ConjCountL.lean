module

public import Init

public section

namespace CFSG.KC.ConjCount

@[expose] def imgW (T : List (List Nat)) (w : List Nat) (p : Nat) : Nat :=
  w.foldr (fun l q => (T.getD l []).getD q 0) p

@[expose] def tabW (T : List (List Nat)) (n : Nat) (w : List Nat) : List Nat :=
  (List.range n).map (imgW T w)

@[expose] def encL (b : Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => x + b * encL b xs

@[expose] def invOK (n : Nat) (x y : List Nat) : Bool :=
  y.length == n && y.all (· < n) && (List.range n).all fun p => x.getD (y.getD p 0) 0 == p

end CFSG.KC.ConjCount
