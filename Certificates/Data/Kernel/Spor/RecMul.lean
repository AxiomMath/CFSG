module

public import Certificates.Data.Kernel.Spor.PEnum

public section

namespace CFSG.KS.RecMul

open CFSG.KS.PEnum

@[expose] noncomputable def mulRf (k : Nat) (POS PL : Nat → Nat) : Nat → Nat → Nat → Nat
  | 0, a, _ => a
  | f + 1, a, b => if b = 0 then a else
      r32 POS (mulRf k POS PL f a (parOf PL b) * k + labOf PL b)

@[expose] noncomputable def oddRf (PL : Nat → Nat) (odd : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => false
  | f + 1, a => if a = 0 then false else xor (oddRf PL odd f (parOf PL a)) (odd (labOf PL a))

@[expose] noncomputable def reachRf (PL : Nat → Nat) : Nat → Nat → Bool
  | 0, b => b == 0
  | f + 1, b => b == 0 || reachRf PL f (parOf PL b)

end CFSG.KS.RecMul
