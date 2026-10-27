module

public section

namespace CFSG.KC.G28R

@[expose] noncomputable def letN (y : Nat) (k : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def letB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def allN (m : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i acc => f i && acc) m

@[expose] noncomputable def anyN (m : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun i acc => f i || acc) m

@[expose] def colM : Nat := 1090785345

@[expose] def maskK : Nat := 68719476735

@[expose] def idK : Nat := 34630287489

@[expose] noncomputable def spK (a k : Nat) : Nat :=
  letN (Nat.land (Nat.shiftRight a k) colM) fun x =>
    Nat.lor x (Nat.lor (Nat.shiftLeft x 1) (Nat.lor (Nat.shiftLeft x 2)
      (Nat.lor (Nat.shiftLeft x 3) (Nat.lor (Nat.shiftLeft x 4) (Nat.shiftLeft x 5)))))

@[expose] noncomputable def rpK (b k : Nat) : Nat :=
  letN (Nat.land (Nat.shiftRight b (Nat.mul 6 k)) 63) fun r =>
    Nat.lor r (Nat.lor (Nat.shiftLeft r 6) (Nat.lor (Nat.shiftLeft r 12)
      (Nat.lor (Nat.shiftLeft r 18) (Nat.lor (Nat.shiftLeft r 24) (Nat.shiftLeft r 30)))))

@[expose] noncomputable def trK (a b k : Nat) : Nat := Nat.land (spK a k) (rpK b k)

@[expose] noncomputable def m2K (a b : Nat) : Nat :=
  letN a fun a => letN b fun b =>
    Nat.land (Nat.xor (trK a b 0) (Nat.xor (trK a b 1) (Nat.xor (trK a b 2)
      (Nat.xor (trK a b 3) (Nat.xor (trK a b 4) (trK a b 5)))))) maskK

@[expose] noncomputable def commK (a b : Nat) : Bool := Nat.beq (m2K a b) (m2K b a)

@[expose] noncomputable def invOK (E IL : Nat → Nat) (N s w : Nat) : Bool :=
  letB (Nat.mod w 1024) fun ii => letB (Nat.mod (Nat.shiftRight w 20) 32768) fun a =>
    letB (Nat.mod (Nat.shiftRight w 35) 32768) fun b => letB (Nat.shiftRight w 50) fun r =>
      Nat.blt ii 315 && Nat.beq (IL ii) s && Nat.blt a N && Nat.blt b N && Nat.blt r 2 &&
        letB (E a) fun g => Nat.beq (m2K g (E b)) idK && Nat.beq (m2K g s) (m2K (IL r) g)

@[expose] noncomputable def o3OK (TL : Nat → Nat) (s w : Nat) : Bool :=
  letB (Nat.mod (Nat.shiftRight w 10) 1024) fun ti => Nat.blt ti 728 && Nat.beq (TL ti) s

@[expose] noncomputable def powOK (E IL TL : Nat → Nat) (N s w s2 s3 s7 s21 : Nat) : Bool :=
  Nat.blt s 68719476736 && (!Nat.beq s21 idK || Nat.beq s3 idK || Nat.beq s7 idK) &&
    (!(Nat.beq s2 idK && !Nat.beq s idK) || invOK E IL N s w) &&
    (!(Nat.beq s3 idK && !Nat.beq s idK) || o3OK TL s w)

@[expose] noncomputable def elemAt (E W IL TL : Nat → Nat) (N k : Nat) : Bool :=
  letB (E k) fun s => letB (m2K s s) fun s2 => letB (m2K s2 s) fun s3 =>
    letB (m2K (m2K s3 s3) s) fun s7 => letB (m2K (m2K s7 s7) s7) fun s21 =>
      powOK E IL TL N s (W k) s2 s3 s7 s21

@[expose] noncomputable def repAt (IL TL CC : Nat → Nat) (r : Nat) : Bool :=
  letB (IL r) fun t =>
    allN 728 (fun i => letB (TL i) fun e =>
      !commK t e || anyN 8 fun m => Nat.beq (CC (Nat.add (Nat.mul 8 r) m)) e) &&
    allN 8 (fun m => letB (CC (Nat.add (Nat.mul 8 r) m)) fun e =>
      allN 8 fun m' => letB (CC (Nat.add (Nat.mul 8 r) m')) fun u =>
        Nat.beq u e || Nat.beq u (m2K e e) || !commK u e) &&
    allN 315 (fun i => letB (IL i) fun t' =>
      Nat.beq t' t || !commK t t' ||
        allN 8 fun m => !commK t' (CC (Nat.add (Nat.mul 8 r) m)))

end CFSG.KC.G28R

end
