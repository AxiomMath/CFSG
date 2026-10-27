module

public import Certificates.Data.Kernel.T10Code
public import Certificates.Data.Kernel.T10CodeAData

public section

namespace CFSG.KC.T10Code

@[expose] noncomputable def maskN (p : Nat → Bool) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun g acc => Nat.lor acc (Nat.shiftLeft (Bool.rec (motive := fun _ => Nat) 0 1 (p g)) g)) n

@[expose] def memO (P : W10) (c x : Nat) : Bool :=
  !Nat.beq (Nat.land (difW (mulW (mulW P (BC c)) (invW P)) (BC x)) ALL) ALL

@[expose] noncomputable def orbOK (P : W10) (D : List (Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun d _ acc => Bool.rec (motive := fun _ => Bool) false acc
      (Nat.beq d.2 (maskN (memO P d.1) 1024))) D

@[expose] noncomputable def labD (D : List (Nat × Nat)) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun d _ acc => Bool.rec (motive := fun _ => Nat) (Nat.succ acc) 0 (tb d.2 x)) D

@[expose] noncomputable def labOK (P : W10) (x : Nat) : Bool :=
  !isInvc P x || Nat.blt (labD orbD x) 25

@[expose] def Kof (i : Nat) : Nat := Nat.land (Nat.shiftRight KALL (Nat.mul 1024 i)) ALL

@[expose] def szOf (i : Nat) : Nat := Nat.land (Nat.shiftRight SZ (Nat.mul 8 i)) 255

@[expose] def tcOf (i : Nat) : Nat := Nat.land (Nat.shiftRight TC (Nat.mul 8 i)) 255

@[expose] def R25 : Nat := 33554431

@[expose] def rowM (i : Nat) : Nat := Nat.land (Nat.shiftRight CT (Nat.mul 25 i)) R25

@[expose] noncomputable def kchk (P : W10) (i : Nat) : Bool :=
  Nat.beq (Kof i) (maskN (fun y => isInvc P y && Nat.beq (labD orbD y) i) 1024)

@[expose] noncomputable def clsOK (P : W10) (i : Nat) : Bool :=
  Nat.beq (szOf i) (cntN (fun x => tb (Kof i) x) 1024) &&
    Nat.beq (tcOf i) (cntN (fun x => tb (Kof i) x && commc P x 64) 1024) &&
    (!tb QB i || Nat.beq (Nat.land (Kof i) (QMW P)) 0)

@[expose] noncomputable def rvec (P : W10) (x : Nat) : Nat :=
  maskN (fun j => Nat.beq (Nat.land (CDW P x) (Kof j)) 0) 25

@[expose] noncomputable def andAcc (p : Nat → Bool) (r : Nat → Nat) (init N : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) init
    (fun x acc => Bool.rec (motive := fun _ => Nat) acc (Nat.land acc (r x)) (p x)) N

@[expose] noncomputable def rowOK (P : W10) (i : Nat) : Bool :=
  Nat.beq (rowM i) (andAcc (fun x => tb (Kof i) x) (rvec P) R25 1024)

@[expose] noncomputable def sumM (f : Nat → Nat) (m n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => Nat.add acc (Bool.rec (motive := fun _ => Nat) 0 (f i) (tb m i))) n

@[expose] noncomputable def allQm (m n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i acc => Bool.rec (motive := fun _ => Bool) false acc (!tb m i || tb QB i)) n

@[expose] noncomputable def leafM (m : Nat) : Bool :=
  !Nat.beq (sumM szOf m 25) 63 || allQm m 25 || Nat.beq (sumM tcOf m 25) 15

@[expose] noncomputable def dfsM (row : Nat → Nat) (Q : Nat → Bool) (L : List Nat) :
    Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool) (fun ch _ => Q ch)
    (fun k _ F ch al => F ch al &&
      (!(tb (row k) k && tb al k) || F (Nat.lor ch (Nat.shiftLeft 1 k)) (Nat.land al (row k)))) L

@[expose] def R25L : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]

end CFSG.KC.T10Code
