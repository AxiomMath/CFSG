module

public import Certificates.Data.Kernel.SporSch.SpanK

public section

namespace CFSG.KS.SpanK

@[expose] noncomputable def stepK3 (f0 f1 f2 : Nat → Nat) (S : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) S (fun a acc => CFSG.KC.Enum.strictN acc fun acc =>
    bif bitK S a then insK (insK (insK acc (f0 a)) (f1 a)) (f2 a) else acc) 256

@[expose] noncomputable def iterK3 (f0 f1 f2 : Nat → Nat) (n S : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun _ ih S => CFSG.KC.Enum.strictN (stepK3 f0 f1 f2 S) ih) n S

end CFSG.KS.SpanK

end
