module

public import CFSG.Certificates.Kernel.Orders.Mat

public section

namespace CFSG.KC.Fi24Syl

open CFSG.KC.Ord CFSG.KC.Loop

@[expose] noncomputable def L7 : Nat :=
  0x1041041041041041041041041041041041041041041041041041041041041041041041041
@[expose] noncomputable def H7 : Nat :=
  0x20820820820820820820820820820820820820820820820820820820820820820820820820
@[expose] noncomputable def CM7 : Nat :=
  0x3f000000000fc000000003f000000000fc000000003f000000000fc000000003f
@[expose] noncomputable def RM : Nat := 0x3ffffffffff
@[expose] noncomputable def ONE7 : Nat :=
  0x1000000000001000000000001000000000001000000000001000000000001000000000001
@[expose] noncomputable def TWO7 : Nat :=
  0x2000000000002000000000002000000000002000000000002000000000002000000000002
@[expose] noncomputable def LV7 : Nat := 0x1041041041
@[expose] noncomputable def HV7 : Nat := 0x20820820820

@[expose] noncomputable def mul7 (A B : Nat) : Nat := mulR 3 6 42 7 3 L7 H7 CM7 RM A B

@[expose] noncomputable def packL (A : List Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun t acc => Nat.add acc (Nat.shiftLeft (A.getD t 0)
      (Nat.add (Nat.mul 42 (Nat.mod t 7)) (Nat.mul 6 (Nat.div t 7))))) 49

@[expose] noncomputable def vecOf (m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun j acc => Nat.add acc (Nat.shiftLeft (Nat.mod (Nat.div m (Nat.pow 3 j)) 3) (Nat.mul 6 j))) 7

@[expose] noncomputable def vecRow (r : Nat) : Nat :=
  Nat.shiftLeft (vecOf (Nat.mod (Nat.add r 1) 2187)) (Nat.mul 42 r)

@[expose] noncomputable def contribK (AV La Ha L31 CMa TL T31 T32 T63 R1 N st : Nat) : Nat :=
  strictN (redP 6 La Ha 3 3 (mulU 6 42 7 CMa RM AV N)) fun Y =>
  strictN (Nat.land (Nat.add Y L31) Ha) fun F1 =>
  strictN (Nat.land (Nat.mul (Nat.shiftRight F1 5) LV7) T63) fun E =>
  strictN (Nat.shiftRight (Nat.sub T32 (Nat.land (Nat.add E T31) T32)) 41) fun Z =>
  strictN (Nat.land (Nat.shiftRight (Nat.mul Z R1) 91812) RM) fun fc =>
  Nat.add (Nat.add st Z)
    (Nat.add (nIf(Nat.ble 243 fc, Nat.shiftLeft Z 21, 0)) (nIf(Nat.ble fc 243, 0, Nat.shiftLeft 1 91854)))

@[expose] noncomputable def stepK (AV La Ha L31 CMa TL T31 T32 T63 R1 M st : Nat) : Nat :=
  strictN (redP 6 L7 H7 3 3 (Nat.add M TWO7)) fun N =>
  nIf(andB (notB (Nat.beq N 0)) (Nat.beq (mul7 (mul7 N N) N) 0),
    contribK AV La Ha L31 CMa TL T31 T32 T63 R1 N st, st)

@[expose] noncomputable def enumK (step : Nat → Nat → Nat) (Ps : List (List Nat)) : Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun acc st => step acc st)
    (fun Pi _ ih acc st => List.rec (motive := fun _ => Nat → Nat) (fun st => st)
      (fun P _ ih2 st => strictN (mul7 acc P) fun M => strictN (ih M st) ih2) Pi st) Ps

@[expose] noncomputable def chunkK (Ps : List (List Nat)) (R : Nat) : Nat :=
  strictN (sumBelow 2187 35 vecRow) fun AV =>
  strictN (rep1 6 15309) fun La =>
  strictN (Nat.mul 32 La) fun Ha =>
  strictN (Nat.mul 31 La) fun L31 =>
  strictN (rep1 42 2187) fun R1 =>
  strictN (Nat.mul 63 R1) fun CMa =>
  strictN (Nat.shiftLeft R1 36) fun TL =>
  strictN (Nat.mul 31 TL) fun T31 =>
  strictN (Nat.mul 32 TL) fun T32 =>
  strictN (Nat.mul 63 TL) fun T63 =>
  enumK (stepK AV La Ha L31 CMa TL T31 T32 T63 R1) Ps R 0

@[expose] noncomputable def pw (T : Nat → Nat) (k : Nat) : List Nat :=
  [ONE7, T k, mul7 (T k) (T k)]

@[expose] noncomputable def PsK (T : Nat → Nat) : List (List Nat) :=
  [pw T 5, pw T 4, pw T 3, pw T 2, pw T 1, pw T 0]

@[expose] noncomputable def RK (T : Nat → Nat) (c : Nat) : Nat :=
  mul7 (mul7 ((pw T 8).getD (Nat.div c 9) 0) ((pw T 7).getD (Nat.mod (Nat.div c 3) 3) 0))
    ((pw T 6).getD (Nat.mod c 3) 0)

@[expose] noncomputable def chunkOK (T : Nat → Nat) (c st : Nat) : Bool :=
  Nat.beq (chunkK (PsK T) (RK T c)) st

@[expose] noncomputable def topsOK (T : Nat → Nat) (As : List (List Nat)) : Bool :=
  andB (Nat.beq As.length 9)
    (Nat.rec (motive := fun _ => Bool) true
      (fun k ih => andB ih (Nat.beq (T k) (packL (As.getD k [])))) 9)

@[expose] noncomputable def cntRows (tot o t : Nat) : Nat :=
  sumBelow 2187 35 fun r =>
    nIf(Nat.ble t (Nat.land (Nat.shiftRight tot (Nat.add (Nat.mul 42 r) o)) 0x1fffff), 1, 0)

@[expose] noncomputable def concl (tot : Nat) : Bool :=
  andB (Nat.blt (Nat.land (Nat.shiftRight tot 91812) 0x1fffff) 6560)
  (andB (Nat.beq (Nat.shiftRight tot 91854) 0)
  (andB (Nat.ble (cntRows tot 0 2186) 26)
  (andB (Nat.ble (cntRows tot 0 728) 80)
    (Nat.ble (cntRows tot 21 242) 242))))

@[expose] noncomputable def totK (st : Nat → Nat) : Nat := sumBelow 27 1 st

end CFSG.KC.Fi24Syl

end
