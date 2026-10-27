module

public import Certificates.Data.Kernel.B3S3K
public import Certificates.Data.Kernel.Spor.RebuildK

public section

namespace CFSG.KC.Co3TK

open CFSG.KC.Enum CFSG.KS CFSG.KC.Misc.ArrEnum CFSG.KC.B3S3K

@[expose] def dig3 (k i : Nat) : Nat := k / 3 ^ i % 3

@[expose] noncomputable def dProdK (P : Nat → Nat) (k : Nat) : Nat :=
  cm 276 9 (pw 276 9 (P 4) (dig3 k 0)) (cm 276 9 (pw 276 9 (P 5) (dig3 k 1))
    (cm 276 9 (pw 276 9 (P 6) (dig3 k 2)) (cm 276 9 (pw 276 9 (P 7) (dig3 k 3))
      (pw 276 9 (P 8) (dig3 k 4)))))

@[expose] noncomputable def dK (P DE : Nat → Nat) : Bool :=
  allN 5 (fun i => permB 276 9 (P (4 + i)) && Nat.beq (pw 276 9 (P (4 + i)) 3) (pidn 276 9)) &&
    allN 5 (fun i => allN 5 fun j =>
      Nat.beq (cm 276 9 (P (4 + i)) (P (4 + j))) (cm 276 9 (P (4 + j)) (P (4 + i)))) &&
    allN 243 (fun k => Nat.beq (DE k) (dProdK P k)) &&
    allN 243 (fun k => allN 243 fun k' => Nat.beq k k' || !Nat.beq (DE k) (DE k'))

@[expose] noncomputable def coordK (DE : Nat → Nat) (G l c : Nat) : Bool :=
  Nat.blt c 243 &&
    Nat.beq (pg 9 (mask 9) (DE c) (pg 9 (mask 9) G 0)) (pg 9 (mask 9) G l) &&
    allN c (fun k => !Nat.beq (pg 9 (mask 9) (DE k) (pg 9 (mask 9) G 0)) (pg 9 (mask 9) G l))

@[expose] def dot3K (m k : Nat) : Nat :=
  (dig3 m 0 * dig3 k 0 + dig3 m 1 * dig3 k 1 + dig3 m 2 * dig3 k 2 + dig3 m 3 * dig3 k 3 +
    dig3 m 4 * dig3 k 4) % 3

@[expose] noncomputable def orthK (CK : Nat → Nat) : Bool :=
  allN 243 fun m => Nat.beq m 0 ||
    !(allN 121 fun j => !(allN 7 fun l => Nat.beq (dot3K m (CK (7 * j + l))) 0))

@[expose] noncomputable def apN (X e p : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) p (fun _ x => pg 9 (mask 9) X x) e

@[expose] noncomputable def fusK (P DE T FW FA FB : Nat → Nat) (k : Nat) : Bool :=
  !Nat.beq (pw 276 9 (T k) 3) (pidn 276 9) || Nat.beq (T k) (pidn 276 9) ||
    (Nat.beq (FW k) 1 && Nat.blt (FA k) 243 && Nat.beq (T k) (DE (FA k))) ||
    (Nat.beq (FW k) 2 && Nat.blt (FA k) 2187 && Nat.blt (FB k) 24 &&
      (if FB k < 12 then Nat.beq (cj 276 9 (T (FA k)) (T k)) (P (12 + FB k))
       else Nat.beq (cj 276 9 (T (FA k)) (T k))
         (cm 276 9 (P (12 + (FB k - 12))) (P (12 + (FB k - 12))))))

@[expose] noncomputable def commPt (A B : Nat) : Bool :=
  allN 276 fun p => Nat.beq (pg 9 (mask 9) A (pg 9 (mask 9) B p)) (pg 9 (mask 9) B (pg 9 (mask 9) A p))

@[expose] noncomputable def cntN (N : Nat) (f : Nat → Bool) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun j acc => Nat.add acc (cond (f j) 1 0)) N

@[expose] noncomputable def classK (N : Nat) (T CW C2 C7 : Nat → Nat) (i : Nat) : Bool :=
  Nat.beq (T i) (pidn 276 9) ||
    (Nat.beq (CW i) 0 && Nat.blt (C2 i) 276 && Nat.blt (C7 i) 276 &&
      !Nat.beq (apN (T i) 2 (C2 i)) (C2 i) && !Nat.beq (apN (T i) 7 (C7 i)) (C7 i)) ||
    Nat.blt (cntN N fun j => commPt (T j) (T i)) 81

end CFSG.KC.Co3TK

end
