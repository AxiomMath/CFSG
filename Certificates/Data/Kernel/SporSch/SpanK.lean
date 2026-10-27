module

public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KS.SpanK

@[expose] noncomputable def bitK (S a : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight S a) (nat_lit 1)) (nat_lit 1)

@[expose] noncomputable def insK (S x : Nat) : Nat :=
  bif bitK S x then S else
    Nat.rec (motive := fun _ => Nat) S (fun a acc => CFSG.KC.Enum.strictN acc fun acc =>
      bif bitK S a then Nat.lor acc (Nat.shiftLeft (nat_lit 1) (Nat.xor a x)) else acc) 256

@[expose] noncomputable def stepK (f0 f1 : Nat → Nat) (S : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) S (fun a acc => CFSG.KC.Enum.strictN acc fun acc =>
    bif bitK S a then insK (insK acc (f0 a)) (f1 a) else acc) 256

@[expose] noncomputable def iterK (f0 f1 : Nat → Nat) (n S : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun _ ih S => CFSG.KC.Enum.strictN (stepK f0 f1 S) ih) n S

@[expose] noncomputable def tabK (T a : Nat) : Nat :=
  Nat.land (Nat.shiftRight T (Nat.mul (nat_lit 8) a)) (nat_lit 255)

end CFSG.KS.SpanK

end
