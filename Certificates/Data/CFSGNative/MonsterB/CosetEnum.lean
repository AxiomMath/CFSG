module

public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model

public section

namespace CFSG.Monster.B.Rep4371.Native.CosetEnum

@[expose] def tabT (e : Nat) (p : Array Nat) : Array Pauli :=
  ((List.range 4096).map fun A => conjPermN p (conjYN e (false, A, 0))).toArray

@[expose] def tabD (e : Nat) (p : Array Nat) : Array Pauli :=
  ((List.range 4096).map fun D => conjPermN p (conjYN e (false, 0, D))).toArray

@[expose] def dec (n : Nat) : Pauli := (n.testBit 24, n % 2 ^ 12, n / 2 ^ 12 % 2 ^ 12)

@[expose] def isOne (x : Pauli) : Bool := !x.1 && x.2.1 % 2 ^ 12 == 0 && x.2.2 % 2 ^ 12 == 0

@[expose] def sqProd (tT tD : Array Pauli) (w y : Pauli) : Pauli :=
  Pauli.mul y (Pauli.mul w (Pauli.mul (y.1, 0, 0) (Pauli.mul tT[y.2.1]! tD[y.2.2]!)))

@[expose] def sqTest (tT tD : Array Pauli) (w : Pauli) (n : Nat) : Bool :=
  let y := dec n
  let t := tT[y.2.1]!
  let u := tD[y.2.2]!
  (y.2.1 ^^^ (w.2.1 ^^^ (0 ^^^ (t.2.1 ^^^ u.2.1)))) % 2 ^ 12 == 0 &&
    (y.2.2 ^^^ (w.2.2 ^^^ (0 ^^^ (t.2.2 ^^^ u.2.2)))) % 2 ^ 12 == 0 &&
    isOne (sqProd tT tD w y)

@[specialize, expose] def countBelow (p : Nat → Bool) : Nat → Nat → Nat
  | 0, acc => acc
  | m + 1, acc => countBelow p m (if p m then acc + 1 else acc)

@[expose] def countSq (tT tD : Array Pauli) (w : Pauli) : Nat :=
  countBelow (sqTest tT tD w) (2 ^ 25) 0

@[expose] def gen (k : Nat) : Pauli :=
  if k < 12 then (false, 2 ^ k, 0) else (false, 0, 2 ^ (k - 12))

@[expose] def gensImg (e : Nat) (p : Array Nat) : Array Pauli :=
  ((List.range 24).map fun k => conjPermN p (conjYN e (gen k))).toArray

@[expose] def inv (x : Pauli) : Pauli := (x.1 ^^ pairN x.2.1 x.2.2, x.2.1, x.2.2)

@[expose] def enc (x : Pauli) : Nat :=
  x.2.1 % 2 ^ 12 + 2 ^ 12 * (x.2.2 % 2 ^ 12) + (if x.1 then 2 ^ 24 else 0)

@[expose] def act (imgs : Array Pauli) (k n : Nat) : Nat :=
  enc (Pauli.mul (inv imgs[k]!) (Pauli.mul (dec n) (gen k)))

end CFSG.Monster.B.Rep4371.Native.CosetEnum
