module

public import CFSG.Certificates.Kernel.Lie.CT.Core

public section

namespace CFSG.KC.F2W

open CFSG.KC.Loop CFSG.KLie.CT

@[expose] noncomputable def mulW (d A B : Nat) : Nat :=
  strictN A fun A => strictN B fun B => strictN (maskN d) fun F =>
  strictN (Nat.div (maskN (Nat.mul d d)) F) fun R =>
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun k acc => Nat.xor acc (Nat.land
    (Nat.mul (Nat.land (Nat.shiftRight A k) R) F)
    (Nat.mul (Nat.land (Nat.shiftRight B (Nat.mul d k)) F) R))) d

end CFSG.KC.F2W

end
