module

public section

namespace CFSG.KC.M24G

@[expose] def byteImg (t : List Nat) (o b : Nat) : Nat :=
  (List.range 8).foldl (fun acc j => if b.testBit j then acc ||| (1 <<< t.getD (o + j) 0) else acc) 0

@[expose] def pack24 : List Nat → Nat
  | [] => 0
  | e :: es => e + pack24 es * 16777216

@[expose] def field24 (P b : Nat) : Nat := (P >>> (24 * b)) % 16777216

@[expose] def byteTab (t : List Nat) (k : Nat) : Nat :=
  pack24 ((List.range 256).map (byteImg t (8 * k)))

@[expose] def imgTab (t : List Nat) : Nat × Nat × Nat := (byteTab t 0, byteTab t 1, byteTab t 2)

@[expose] def imgF (bt : Nat × Nat × Nat) (m : Nat) : Nat :=
  field24 bt.1 (m % 256) ||| field24 bt.2.1 ((m >>> 8) % 256) ||| field24 bt.2.2 ((m >>> 16) % 256)

end CFSG.KC.M24G
