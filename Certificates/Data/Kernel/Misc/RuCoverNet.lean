module

public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.Misc.RuCoverNet

open CFSG.KC.Loop

@[expose] noncomputable def line (A : Nat → Nat) (c m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => strictN acc (fun a =>
      Nat.lor a (Nat.shiftLeft (A (Nat.add (Nat.mul i (nat_lit 6)) c)) (Nat.mul (nat_lit 32) i))))
    m

@[expose] noncomputable def F (A : Nat → Nat) (c : Nat) : Nat := line A c (nat_lit 16240)

end CFSG.KC.Misc.RuCoverNet

end
