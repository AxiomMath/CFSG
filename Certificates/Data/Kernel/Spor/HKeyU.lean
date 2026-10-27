module

public import Certificates.Data.Kernel.Spor.HKeyB

public section

namespace CFSG.KS.MulH

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def hk4 (w m B h : Nat) : Nat :=
  hkStep (hkStep (hkStep (hkStep h (Nat.land B m)) (Nat.land (Nat.shiftRight B w) m))
    (Nat.land (Nat.shiftRight B (Nat.mul (nat_lit 2) w)) m))
    (Nat.land (Nat.shiftRight B (Nat.mul (nat_lit 3) w)) m)

@[expose] noncomputable def hkU8 (w m k : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ h => h)
    (fun _ ih B h => strictN (Nat.shiftRight B (Nat.mul (nat_lit 8) w))
      (fun B' => strictN (hk4 w m (Nat.shiftRight B (Nat.mul (nat_lit 4) w)) (hk4 w m B h))
        (fun h' => ih B' h'))) k

@[expose] noncomputable def hkBlU (w m X : Nat) (nb : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ h => h)
    (fun _ ih j h => strictN (hkU8 w m (nat_lit 8) (blk64 w X j) h)
      (fun h' => ih (Nat.succ j) h')) nb

@[expose] noncomputable def hkeyU (n w m X : Nat) : Nat :=
  strictN (hkBlU w m X (Nat.shiftRight n (nat_lit 6)) (nat_lit 0) (nat_lit 14695981039346656037))
    (fun h => hkGo w m (Nat.shiftRight X (Nat.mul (Nat.mul w (nat_lit 64)) (Nat.shiftRight n (nat_lit 6))))
      (Nat.land n (nat_lit 63)) (nat_lit 0) h)

end CFSG.KS.MulH

end
