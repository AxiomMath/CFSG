module

public import Certificates.Data.Kernel.Misc.Lines

public section

namespace CFSG.KC.Misc.Xi

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.Misc.O73 CFSG.KC.Misc.T46
  CFSG.KC.Misc.Polar CFSG.KC.Misc.Lines

@[expose] noncomputable def imgP (T M : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => Nat.lor acc (Nat.shiftLeft 1 (at' 10 T (at' 10 M i)))) 126

@[expose] noncomputable def listsP (S M : Nat) : Bool :=
  andB (Nat.blt S (Nat.shiftLeft 1 693)) <| andB (Nat.blt M (Nat.shiftLeft 1 1260)) <|
  andB (Nat.beq (Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => Nat.lor acc (Nat.shiftLeft 1 (at' 10 M i))) 126) S) <|
  andB (Nat.blt (at' 10 M 125) 693) <|
    allN 125 fun i => Nat.blt (at' 10 M i) (at' 10 M (Nat.succ i))

@[expose] noncomputable def tabK (UP : Nat) (TP : Nat → Nat) (lo n : Nat) : Bool :=
  allN n fun d => letB (Nat.add lo d) fun f => impB (Nat.blt f 693) (genK UP (at' 12 UP f) (TP f))

@[expose] noncomputable def nzK (c : Nat) : Nat := weightK c

@[expose] noncomputable def prodK (c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 1 (fun i acc => f4K acc (crdK c i)) 6

@[expose] noncomputable def rootK (UP c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun p acc => letN (at' 12 UP p) fun v =>
    Bool.rec (motive := fun _ => Nat) acc (Nat.lor acc (Nat.shiftLeft 1 p))
      (orB (Nat.beq (nzK v) 2) (andB (Nat.beq (nzK v) 6) (Nat.beq (prodK v) c)))) 693

@[expose] noncomputable def memK (HS ML : Nat → Nat) (lo n : Nat) : Bool :=
  allN n fun d => letB (Nat.add lo d) fun k => impB (Nat.blt k 4224) (listsP (HS k) (ML k))

@[expose] noncomputable def distinctK (HS : Nat → Nat) (SP : List Nat) : Bool :=
  andB (Nat.beq (lenN SP) 4224) <|
  andB (Nat.beq (List.rec (motive := fun _ => Nat) 0 (fun k _ ih => Nat.lor ih (Nat.shiftLeft 1 k)) SP)
    (Nat.sub (Nat.shiftLeft 1 4224) 1)) <|
    List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun k _ ih prev => letB (HS k) fun s => andB (Nat.blt prev (Nat.succ s)) (ih (Nat.succ s)))
      SP 0

@[expose] noncomputable def orbK (UP X Y : Nat) (HS ML : Nat → Nat) (J : Nat)
    (o c : Nat) : Bool :=
  andB (Nat.beq (HS (Nat.mul 1408 o)) (rootK UP c)) <|
  Nat.beq (Nat.rec (motive := fun _ => Nat) 2 (fun h acc => Nat.rec (motive := fun _ => Nat) acc
    (fun l acc2 => step h l acc2) 2) 1408) 1409
where
  step (h l cnt : Nat) : Nat :=
    letN cnt fun cnt => letN (at' 11 J (Nat.add (Nat.mul 2 h) l)) fun j =>
    Bool.rec (motive := fun _ => Nat) 0
      (Bool.rec (motive := fun _ => Nat) cnt (Nat.succ cnt) (Nat.beq (Nat.succ j) cnt))
      (andB (andB (Nat.blt 0 cnt) (Nat.blt h (Nat.pred cnt))) <|
        andB (Nat.blt j cnt) <|
          Nat.beq (HS (Nat.add (Nat.mul 1408 o) j))
            (imgP (Bool.rec (motive := fun _ => Nat) X Y (Nat.beq l 1)) (ML (Nat.add (Nat.mul 1408 o) h))))

@[expose] noncomputable def rowsK (TP HS ML RW AB : Nat → Nat) (lo n : Nat) : Bool :=
  allN n fun d => letB (Nat.add lo d) fun k => impB (Nat.blt k 1408) <|
    letB (HS k) fun S => letB (ML k) fun M => letB (RW k) fun R =>
    andB (Nat.blt R (Nat.shiftLeft 1 (Nat.mul 11 693))) <|
    andB (allN 693 fun f => letB (at' 11 R f) fun i => Bool.rec (motive := fun _ => Bool)
      (andB (Nat.blt i 1408) <| andB (notB (Nat.beq i k)) <| Nat.beq (HS i) (imgP (TP f) M))
      (Nat.beq i k) (bitK S f)) <|
    letB (Nat.rec (motive := fun _ => Nat) 0 (fun f acc => Bool.rec (motive := fun _ => Nat)
      (Nat.add acc (Nat.shiftLeft 1 (at' 11 R f))) acc (bitK S f)) 693) fun sm =>
    andB (Nat.beq sm (AB k)) <|
      Nat.beq (Nat.rec (motive := fun _ => Nat) 0 (fun f acc => Bool.rec (motive := fun _ => Nat)
        (Nat.lor acc (Nat.shiftLeft 1 (at' 11 R f))) acc (bitK S f)) 693) sm

@[expose] noncomputable def conjK (TP : Nat → Nat) (X Y : Nat) (lo n : Nat) : Bool :=
  letB (compP 693 10 Y Y) fun Y2 => allN n fun d => letB (Nat.add lo d) fun p =>
    impB (Nat.blt p 693) <| letB (TP p) fun T =>
      andB (Nat.beq (compP 693 10 X (compP 693 10 T X)) (TP (at' 10 X p)))
        (Nat.beq (compP 693 10 Y (compP 693 10 T Y2)) (TP (at' 10 Y p)))

@[expose] noncomputable def paK (J PA : Nat) : Bool :=
  allN 1407 fun d => letB (Nat.succ d) fun k => letB (at' 12 PA k) fun e =>
    andB (Nat.blt e 2816) (Nat.beq (at' 11 J e) k)

@[expose] noncomputable def rowsR (HS RW AB : Nat → Nat) (X Y J PA : Nat) (lo n : Nat) : Bool :=
  letB (compP 693 10 Y Y) fun Y2 => allN n fun d => letB (Nat.add lo d) fun k =>
    impB (andB (Nat.blt 0 k) (Nat.blt k 1408)) <|
    letB (HS k) fun S => letB (RW k) fun R => letB (at' 12 PA k) fun e =>
    letB (RW (Nat.div e 2)) fun Rp => letB (Nat.mod e 2) fun l =>
    letB (Bool.rec (motive := fun _ => Nat) X Y2 (Nat.beq l 1)) fun G =>
    andB (Nat.blt R (Nat.shiftLeft 1 (Nat.mul 11 693))) <|
    andB (allN 693 fun f => letB (at' 11 R f) fun i => Bool.rec (motive := fun _ => Bool)
      (andB (Nat.blt i 1408) <| andB (notB (Nat.beq i k)) <|
        Nat.beq i (at' 11 J (Nat.add (Nat.mul 2 (at' 11 Rp (at' 10 G f))) l)))
      (Nat.beq i k) (bitK S f)) <|
    letB (Nat.rec (motive := fun _ => Nat) 0 (fun f acc => Bool.rec (motive := fun _ => Nat)
      (Nat.add acc (Nat.shiftLeft 1 (at' 11 R f))) acc (bitK S f)) 693) fun sm =>
    andB (Nat.beq sm (AB k)) <|
      Nat.beq (Nat.rec (motive := fun _ => Nat) 0 (fun f acc => Bool.rec (motive := fun _ => Nat)
        (Nat.lor acc (Nat.shiftLeft 1 (at' 11 R f))) acc (bitK S f)) 693) sm

@[expose] noncomputable def symK (AB : Nat → Nat) (lo n : Nat) : Bool :=
  allN n fun d => letB (Nat.add lo d) fun x => impB (Nat.blt x 1408) <| letB (AB x) fun Ax =>
    allN 1408 fun v => Bool.rec (motive := fun _ => Bool) (notB (bitK (AB v) x)) (bitK (AB v) x)
      (bitK Ax v)

@[expose] noncomputable def pop1408 (S : Nat) : Nat :=
  letN S fun S => Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => Nat.add acc (Nat.land (Nat.shiftRight S i) 1)) 1408

@[expose] noncomputable def interK (HS AB PB : Nat → Nat) : Bool :=
  letB (HS 0) fun H0 => letB (AB 0) fun A0 =>
  andB (allN 1407 fun d => letB (Nat.succ d) fun i =>
    Nat.beq (popK (Nat.land H0 (HS i))) (Bool.rec (motive := fun _ => Nat) 18 30 (bitK A0 i))) <|
    allL [0, 1408, 2816] fun off => letB (HS off) fun R =>
      allN 693 fun f => orB (bitK R f) (Nat.beq (popK (Nat.land R (PB f))) 30)

@[expose] noncomputable def diamK (AB : Nat → Nat) (lo n : Nat) : Bool :=
  letB (AB 0) fun A0 => allN n fun d => letB (Nat.add lo d) fun v =>
    impB (andB (Nat.blt 0 v) (andB (Nat.blt v 1408) (notB (bitK A0 v)))) <|
    letB (Nat.land A0 (AB v)) fun C => andB (notB (Nat.beq C 0)) <|
      allN 1408 fun w => impB (andB (Nat.blt 0 w) (andB (notB (bitK A0 w)) (bitK (AB v) w)))
        (notB (Nat.beq (Nat.land C (AB w)) 0))

@[expose] noncomputable def muK (AB MT : Nat → Nat) (lo n : Nat) : Bool :=
  letB (AB 0) fun A0 => allN n fun d => letB (Nat.add lo d) fun v =>
    impB (andB (Nat.blt 0 v) (andB (Nat.blt v 1408) (notB (bitK A0 v)))) <|
    letB (Nat.land A0 (AB v)) fun C => letB (MT v) fun Mv => letB (at' 11 Mv 0) fun m =>
      andB (notB (Nat.beq m 0)) <|
      andB (Nat.beq (Nat.rec (motive := fun _ => Nat) 0
        (fun i acc => Nat.lor acc (Nat.shiftLeft 1 (at' 11 Mv (Nat.succ i)))) m) C) <|
        Nat.beq (Nat.rec (motive := fun _ => Nat) (Nat.shiftLeft 1 1408)
          (fun i seen => letN seen fun seen => Bool.rec (motive := fun _ => Nat) 0
          (Nat.lor seen (Nat.shiftLeft 1 (at' 11 Mv (Nat.succ i))))
          (andB (Nat.blt 0 seen) (orB (Nat.beq i 0)
            (notB (Nat.beq (Nat.land seen (AB (at' 11 Mv (Nat.succ i)))) 0))))) m) 0
          |> notB

end CFSG.KC.Misc.Xi

end
