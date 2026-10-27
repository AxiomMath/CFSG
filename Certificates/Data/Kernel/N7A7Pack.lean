module

public import Mathlib.Data.Nat.Bitwise

public section

namespace CFSG.KernelN7

@[expose] def dig (p j : Nat) : Nat := p / 8 ^ j % 8

@[expose] def compP (p q : Nat) : Nat :=
  dig p (dig q 0) + 8 * dig p (dig q 1) + 64 * dig p (dig q 2) + 512 * dig p (dig q 3) +
    4096 * dig p (dig q 4) + 32768 * dig p (dig q 5) + 262144 * dig p (dig q 6)

@[expose] def idP : Nat := 0 + 8 * 1 + 64 * 2 + 512 * 3 + 4096 * 4 + 32768 * 5 + 262144 * 6

@[expose] def wordP (P Q : Nat) : List Nat → Nat
  | [] => idP
  | l :: w => compP (if l = 0 then P else Q) (wordP P Q w)

@[expose] def noDupB : List Nat → Nat → Bool
  | [], _ => true
  | x :: xs, m => !m.testBit x && noDupB xs (m ||| 2 ^ x)

end CFSG.KernelN7
