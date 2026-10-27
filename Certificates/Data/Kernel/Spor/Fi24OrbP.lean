module

public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.Fi24Orb

open CFSG.KC.Loop

@[expose] noncomputable def pow29 (mul : Nat → Nat → Nat) (X : Nat) : Nat :=
  strictN (mul X X) (fun x2 => strictN (mul x2 x2) (fun x4 => strictN (mul x4 x4) (fun x8 =>
    strictN (mul x8 x8) (fun x16 => mul x16 (mul x8 (mul x4 X))))))

end CFSG.KC.Fi24Orb

end
