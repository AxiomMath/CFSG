module

public section

namespace CFSG.F4.Native

@[expose] def f4mul (x y : Nat) : Nat :=
  let a0 := x % 2
  let a1 := x / 2
  let b0 := y % 2
  let b1 := y / 2
  (a0 * b0 + a1 * b1) % 2 + 2 * ((a0 * b1 + a1 * b0 + a1 * b1) % 2)

@[expose] def coord (c i : Nat) : Nat := (c / 4 ^ i) % 4

@[expose] def hermC (c d : Nat) : Nat :=
  (List.range 6).foldl (fun acc i => acc ^^^ f4mul (coord c i) (f4mul (coord d i) (coord d i))) 0

@[expose] def eC (i : Nat) : Nat := 4 ^ i

@[expose] def candC (i c : Nat) : Bool :=
  hermC c c == hermC (eC i) (eC i) &&
    (List.range i).all (fun j => hermC (eC j) c == hermC (eC j) (eC i) &&
      hermC c (eC j) == hermC (eC i) (eC j)) &&
    (List.range 6).any (fun k => decide (i ≤ k) && coord c k != 0)

@[expose] def countC (i : Nat) : Nat := (List.range 4096).countP (candC i)

end CFSG.F4.Native
