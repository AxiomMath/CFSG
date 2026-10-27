module

public import Certificates.Data.Kernel.O8.Nat8
public import Certificates.Data.Kernel.Spor.Raw

public section

namespace CFSG.KC.O8F

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.O8
open CFSG.KC.Enum (pg)
open CFSG.KS (mask)

@[expose] noncomputable def arrEqK (n w : Nat) (t : Array Nat) (P : Nat) : Bool :=
  bAnd(Nat.beq t.size n, CFSG.KLie.CT.allN n fun i => Nat.beq (t.getD i 0) (pg w (mask w) P i))

@[expose] noncomputable def packA (n w : Nat) (t : Array Nat) : Nat :=
  orN n fun i => Nat.shiftLeft (t.getD i 0) (Nat.mul w i)

@[expose] noncomputable def fnK (NS NI : Nat) (f : Nat → Nat) : Nat :=
  orN (nat_lit 136) fun i => Nat.shiftLeft (nsMap NS NI f i) (Nat.mul (nat_lit 8) i)

@[expose] noncomputable def fnLtK (NS : Nat) (f : Nat → Nat) : Bool :=
  CFSG.KLie.CT.allN (nat_lit 136) fun i => Nat.blt (f (fget NS i (nat_lit 8))) (nat_lit 256)

@[expose] def permBitsT (l : List Nat) (u : Nat) : Nat :=
  (List.range 5).foldl (fun acc i => if u.testBit i then acc ^^^ 2 ^ (l.getD i 0) else acc) 0

@[expose] def sgnT (l : List Nat) : Int :=
  ((List.range 5).flatMap fun i => (List.range 5).filterMap fun j =>
    if i < j then some (if l.getD i 0 < l.getD j 0 then (1 : Int) else -1) else none).prod

end CFSG.KC.O8F

end
