module

public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.PopF

open CFSG.KC.Loop

@[expose] noncomputable def onesF (n : Nat) : Nat := Nat.sub (Nat.shiftLeft (nat_lit 1) n) (nat_lit 1)

@[expose] noncomputable def lowM (W k : Nat) : Nat :=
  Nat.mul (Nat.div (onesF W) (onesF (Nat.shiftLeft (nat_lit 2) k))) (onesF (Nat.shiftLeft (nat_lit 1) k))

@[expose] noncomputable def stepF (W k y : Nat) : Nat :=
  (fun m => Nat.add (Nat.land y m) (Nat.land (Nat.shiftRight y (Nat.shiftLeft (nat_lit 1) k)) m)) (lowM W k)

@[expose] noncomputable def runF (W n : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ x => x)
    (fun _ ih i x => strictN (stepF W i x) (ih (Nat.add i (nat_lit 1)))) n

@[expose] noncomputable def pcF (L y : Nat) : Nat := runF (Nat.shiftLeft (nat_lit 1) L) L (nat_lit 0) y

end CFSG.KC.PopF

end
