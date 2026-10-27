module

public import Certificates.Data.Kernel.Spor.MulH

public section

namespace CFSG.KS.MulH

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def blk64 (w X j : Nat) : Nat :=
  fld(X, Nat.mul (Nat.mul w (nat_lit 64)) j, mask (Nat.mul w (nat_lit 64)))

@[expose] noncomputable def hkBl (w m X : Nat) (nb : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ h => h)
    (fun _ ih j h => strictN (hkGo w m (blk64 w X j) (nat_lit 64) (nat_lit 0) h)
      (fun h' => ih (Nat.succ j) h')) nb

@[expose] noncomputable def hkeyB (n w m X : Nat) : Nat :=
  strictN (hkBl w m X (Nat.shiftRight n (nat_lit 6)) (nat_lit 0) (nat_lit 14695981039346656037))
    (fun h => hkGo w m (Nat.shiftRight X (Nat.mul (Nat.mul w (nat_lit 64)) (Nat.shiftRight n (nat_lit 6))))
      (Nat.land n (nat_lit 63)) (nat_lit 0) h)

end CFSG.KS.MulH

end
