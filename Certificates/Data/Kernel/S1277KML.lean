module

public import Certificates.Data.Kernel.S1277KGm

public section

namespace CFSG.KC.S1277ML

@[expose] noncomputable def andB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) false b a

@[expose] noncomputable def orB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) b true a

@[expose] noncomputable def notB (a : Bool) : Bool := Bool.rec (motive := fun _ => Bool) true false a

@[expose] noncomputable def eqB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) (notB b) b a

@[expose] noncomputable def strictB (y : ℕ) (k : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def allL (f : ℕ → Bool) (l : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ r => andB (f x) r) l

@[expose] noncomputable def anyL (f : ℕ → Bool) (l : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun x _ r => orB (f x) r) l

@[expose] noncomputable def filtL (f : ℕ → Bool) (l : List ℕ) : List ℕ :=
  List.rec (motive := fun _ => List ℕ) [] (fun x _ r => Bool.rec (motive := fun _ => List ℕ) r
    (x :: r) (f x)) l

@[expose] noncomputable def cntL (f : ℕ → Bool) (l : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) (nat_lit 0) (fun x _ r => Bool.rec (motive := fun _ => ℕ) r
    (Nat.succ r) (f x)) l

@[expose] noncomputable def maskF (f : ℕ → ℕ) (l : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) (nat_lit 0)
    (fun x _ r => Nat.lor (Nat.shiftLeft (nat_lit 1) (f x)) r) l

@[expose] noncomputable def allBelow (f : ℕ → Bool) (n : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun c r => andB (f c) r) n

@[expose] noncomputable def maskBelow (f : ℕ → Bool) (n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (nat_lit 0)
    (fun c r => Bool.rec (motive := fun _ => ℕ) r (Nat.lor (Nat.shiftLeft (nat_lit 1) c) r) (f c)) n

@[expose] noncomputable def bitsBelow (m : ℕ) (n : ℕ) (acc : List ℕ) : List ℕ :=
  Nat.rec (motive := fun _ => List ℕ → List ℕ) (fun acc => acc)
    (fun c r acc => r (Bool.rec (motive := fun _ => List ℕ) acc (c :: acc)
      (Nat.blt (nat_lit 0) (Nat.land m (Nat.shiftLeft (nat_lit 1) c))))) n acc

@[expose] noncomputable def fldN (p s : ℕ) : ℕ := Nat.land (Nat.shiftRight p s) (nat_lit 63)

@[expose] noncomputable def bit1 (v i : ℕ) : ℕ := Nat.land (Nat.shiftRight v i) (nat_lit 1)

@[expose] noncomputable def appQ (p v : ℕ) : ℕ :=
  Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor
    (Nat.mul (Nat.land p (nat_lit 63)) (Nat.land v (nat_lit 1)))
    (Nat.mul (fldN p (nat_lit 6)) (bit1 v (nat_lit 1))))
    (Nat.mul (fldN p (nat_lit 12)) (bit1 v (nat_lit 2))))
    (Nat.mul (fldN p (nat_lit 18)) (bit1 v (nat_lit 3))))
    (Nat.mul (fldN p (nat_lit 24)) (bit1 v (nat_lit 4))))
    (Nat.mul (fldN p (nat_lit 30)) (bit1 v (nat_lit 5)))

@[expose] noncomputable def bitN (m i : ℕ) : Bool :=
  Nat.blt (nat_lit 0) (Nat.land m (Nat.shiftLeft (nat_lit 1) i))

@[expose] noncomputable def pcN (m : ℕ) : ℕ :=
  (fun x1 => (fun x2 =>
      (fun x3 => Nat.shiftRight (Nat.land (Nat.mul x3 (nat_lit 72340172838076673))
        (nat_lit 18446744073709551615)) (nat_lit 56))
      (Nat.land (Nat.add x2 (Nat.shiftRight x2 (nat_lit 4))) (nat_lit 1085102592571150095)))
    (Nat.add (Nat.land x1 (nat_lit 3689348814741910323))
      (Nat.land (Nat.shiftRight x1 (nat_lit 2)) (nat_lit 3689348814741910323))))
  (Nat.sub m (Nat.land (Nat.shiftRight m (nat_lit 1)) (nat_lit 6148914691236517205)))

@[expose] noncomputable def sigP (p : ℕ) : ℕ :=
  Nat.xor p (Nat.shiftLeft (Nat.land p (nat_lit 1057222719)) (nat_lit 6))

@[expose] noncomputable def isIdP (p : ℕ) : Bool := Nat.beq p (nat_lit 34630287489)

@[expose] noncomputable def isInvP (p : ℕ) : Bool :=
  andB (Nat.beq (appQ p (Nat.land p (nat_lit 63))) (nat_lit 1)) <|
  andB (Nat.beq (appQ p (fldN p (nat_lit 6))) (nat_lit 2)) <|
  andB (Nat.beq (appQ p (fldN p (nat_lit 12))) (nat_lit 4)) <|
  andB (Nat.beq (appQ p (fldN p (nat_lit 18))) (nat_lit 8)) <|
  andB (Nat.beq (appQ p (fldN p (nat_lit 24))) (nat_lit 16)) <|
  andB (Nat.beq (appQ p (fldN p (nat_lit 30))) (nat_lit 32)) (notB (isIdP p))

@[expose] noncomputable def fixMP (p : ℕ) : ℕ := maskBelow (fun c => Nat.beq (appQ p c) c) (nat_lit 64)

@[expose] noncomputable def imgM (S : List ℕ) (c : ℕ) : ℕ := maskF (fun p => appQ p c) S

@[expose] noncomputable def osChk (P : List ℕ) (m18 m45 : ℕ) : Bool :=
  allBelow (fun c => strictB (pcN (imgM P c)) fun k =>
    andB (eqB (Nat.beq k (nat_lit 18)) (bitN m18 c)) (eqB (Nat.beq k (nat_lit 45)) (bitN m45 c)))
    (nat_lit 64)

@[expose] noncomputable def invL (Q : List ℕ) : List ℕ :=
  List.rec (motive := fun _ => List ℕ) []
    (fun p _ r => Bool.rec (motive := fun _ => List ℕ) r (fixMP p :: r) (isInvP p)) Q

@[expose] noncomputable def stabL (Q : List ℕ) (m : ℕ) (dl : List ℕ) : List ℕ :=
  filtL (fun p => allL (fun d => bitN m (appQ p d)) dl) Q

@[expose] noncomputable def stabFacts (S : List ℕ) (m m18 m45 : ℕ) : Bool :=
  strictB (Nat.land m m18) fun t18 =>
    andB (Nat.ble (nat_lit 4) (pcN t18)) <|
    andB (allL (fun t => Nat.beq (Nat.land t18 (imgM S t)) t18) (bitsBelow t18 (nat_lit 64) []))
      (anyL (fun c => Nat.ble (nat_lit 9) (pcN (imgM S c)))
        (bitsBelow (Nat.land m m45) (nat_lit 64) []))

@[expose] noncomputable def cntSup (L : List ℕ) (m : ℕ) : ℕ :=
  cntL (fun m' => Nat.beq (Nat.land m m') m) L

@[expose] noncomputable def perDP (Q L : List ℕ) (m m18 m45 : ℕ) : Bool :=
  strictB (cntSup L m) fun k =>
    andB (Nat.ble k (nat_lit 3))
      (orB (Nat.blt k (nat_lit 3)) (stabFacts (stabL Q m (bitsBelow m (nat_lit 64) [])) m m18 m45))

@[expose] noncomputable def mChkI (Q L : List ℕ) (m18 m45 : ℕ) : Bool :=
  andB (allL (fun m => Nat.ble (pcN m) (nat_lit 16)) L)
    (allL (fun m => orB (notB (Nat.beq (pcN m) (nat_lit 16))) (perDP Q L m m18 m45)) L)

@[expose] noncomputable def mChk (Q : List ℕ) (m18 m45 : ℕ) : Bool := mChkI Q (invL Q) m18 m45

end CFSG.KC.S1277ML

end
