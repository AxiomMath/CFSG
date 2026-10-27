module

public section

namespace CFSG.Sp43.Native

set_option compiler.extract_closed false

@[expose] def dig (c k : Nat) : Nat := c / 3 ^ k % 3

@[expose] def horner : List Nat → Nat
  | [] => 0
  | a :: l => a % 3 + 3 * horner l

@[expose] def ent (c i j : Nat) : Nat := dig c (4 * i + j)

@[expose] def mulC (a b : Nat) : Nat :=
  horner ((List.range 16).map fun k =>
    ent a (k / 4) 0 * ent b 0 (k % 4) + ent a (k / 4) 1 * ent b 1 (k % 4) +
      ent a (k / 4) 2 * ent b 2 (k % 4) + ent a (k / 4) 3 * ent b 3 (k % 4))

@[expose] def digs (c : Nat) : Array Nat := (Array.range 16).map fun k => c / 3 ^ k % 3

@[expose] def mulF (a b : Nat) : Nat :=
  let x := digs a
  let y := digs b
  horner ((List.range 16).map fun k =>
    x[4 * (k / 4)]! * y[k % 4]! + x[4 * (k / 4) + 1]! * y[4 + k % 4]! +
      x[4 * (k / 4) + 2]! * y[8 + k % 4]! + x[4 * (k / 4) + 3]! * y[12 + k % 4]!)

@[expose] def oneC : Nat := horner [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]

@[expose] def powC (a : Nat) : Nat → Nat
  | 0 => oneC
  | e + 1 => mulC (powC a e) a

@[expose] def vecC (c v : Nat) : Nat :=
  horner ((List.range 4).map fun i =>
    ent c i 0 * dig v 0 + ent c i 1 * dig v 1 + ent c i 2 * dig v 2 + ent c i 3 * dig v 3)

@[expose] def omg (x y : Nat) : Nat :=
  (2 * (dig x 0 * dig y 2) + 2 * (dig x 1 * dig y 3) + dig x 2 * dig y 0 + dig x 3 * dig y 1) % 3

@[expose] def spCodes (_ : Unit := ()) : List Nat :=
  (List.range 81).flatMap fun r3 =>
  ((List.range 81).filter fun r2 => omg r2 r3 == 0).flatMap fun r2 =>
  ((List.range 81).filter fun r1 => omg r1 r2 == 0 && omg r1 r3 == 2).flatMap fun r1 =>
  ((List.range 81).filter fun r0 => omg r0 r1 == 0 && omg r0 r2 == 2 && omg r0 r3 == 0).map
    fun r0 => r0 + 81 * r1 + 6561 * r2 + 531441 * r3

end CFSG.Sp43.Native

end
