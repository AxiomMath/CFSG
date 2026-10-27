module

public section

namespace CFSG.GL33.Native

set_option compiler.extract_closed false

@[expose] def dig (c k : Nat) : Nat := c / 3 ^ k % 3

@[expose] def horner : List Nat → Nat
  | [] => 0
  | a :: l => a % 3 + 3 * horner l

@[expose] def ent (c i j : Nat) : Nat := dig c (3 * i + j)

@[expose] def mulC (a b : Nat) : Nat := horner ((List.range 9).map fun k =>
  ent a (k / 3) 0 * ent b 0 (k % 3) + ent a (k / 3) 1 * ent b 1 (k % 3) +
    ent a (k / 3) 2 * ent b 2 (k % 3))

@[expose] def digs (c : Nat) : Array Nat := (Array.range 9).map fun k => c / 3 ^ k % 3

@[expose] def mulF (a b : Nat) : Nat :=
  let x := digs a
  let y := digs b
  horner ((List.range 9).map fun k =>
    x[3 * (k / 3)]! * y[k % 3]! + x[3 * (k / 3) + 1]! * y[3 + k % 3]! +
      x[3 * (k / 3) + 2]! * y[6 + k % 3]!)

@[expose] def oneC : Nat := horner [1, 0, 0, 0, 1, 0, 0, 0, 1]

@[expose] def powC (a : Nat) : Nat → Nat
  | 0 => oneC
  | e + 1 => mulC (powC a e) a

@[expose] def vecC (c v : Nat) : Nat := horner ((List.range 3).map fun i =>
  ent c i 0 * dig v 0 + ent c i 1 * dig v 1 + ent c i 2 * dig v 2)

@[expose] def covC (f c : Nat) : Nat := horner ((List.range 3).map fun j =>
  dig f 0 * ent c 0 j + dig f 1 * ent c 1 j + dig f 2 * ent c 2 j)

@[expose] def detC (c : Nat) : Nat :=
  (ent c 0 0 * ent c 1 1 * ent c 2 2 + ent c 0 1 * ent c 1 2 * ent c 2 0 +
      ent c 0 2 * ent c 1 0 * ent c 2 1 +
    2 * (ent c 0 2 * ent c 1 1 * ent c 2 0 + ent c 0 1 * ent c 1 0 * ent c 2 2 +
      ent c 0 0 * ent c 1 2 * ent c 2 1)) % 3

@[expose] def glCodes (_ : Unit := ()) : List Nat :=
  (List.range 19683).filter fun c => detC c != 0

end CFSG.GL33.Native

end
