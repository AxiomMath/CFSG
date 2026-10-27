module

public import Certificates.Data.Kernel.U6.Orb

public section

namespace CFSG.KC.U6

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2

@[expose] noncomputable def keyP (x : Nat) : Nat :=
  Nat.add (Nat.mul (ap10 x (nat_lit 1)) (nat_lit 1024)) (ap10 x (nat_lit 3))

@[expose] noncomputable def keysK (TE : Nat) : Nat :=
  sumN (nat_lit 64) fun j => Nat.shiftLeft (keyP (elt TE j)) (Nat.mul (nat_lit 20) j)

@[expose] noncomputable def idxK (KY k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 64)
    (fun i acc => (fun j => nIf(Nat.beq (fget KY j (nat_lit 20)) k, j, acc))
      (Nat.sub (nat_lit 63) i))
    (nat_lit 64)

@[expose] noncomputable def mulK (TE KY i j : Nat) : Nat :=
  strictN (elt TE i) fun x => strictN (elt TE j) fun y =>
    idxK KY (Nat.add (Nat.mul (ap10 x (ap10 y (nat_lit 1))) (nat_lit 1024))
      (ap10 x (ap10 y (nat_lit 3))))

@[expose] noncomputable def mulTab (TE KY : Nat) : Nat :=
  sumBelow (nat_lit 4096) (nat_lit 64) fun k =>
    Nat.shiftLeft (mulK TE KY (Nat.shiftRight k (nat_lit 6)) (Nat.land k (nat_lit 63)))
      (Nat.mul (nat_lit 7) k)

@[expose] noncomputable def mu (MU i j : Nat) : Nat :=
  fget MU (Nat.add (Nat.mul (nat_lit 64) i) j) (nat_lit 7)

@[expose] noncomputable def mapV (X v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => strictN acc fun acc =>
      nIf(Nat.beq (fget v i (nat_lit 1)) (nat_lit 1), Nat.xor acc (fget X i (nat_lit 9)), acc))
    (nat_lit 9)

@[expose] noncomputable def mcomp (X Y : Nat) : Nat :=
  sumN (nat_lit 9) fun i => Nat.shiftLeft (mapV X (fget Y i (nat_lit 9))) (Nat.mul (nat_lit 9) i)

@[expose] noncomputable def mId : Nat :=
  sumN (nat_lit 9) fun i => Nat.shiftLeft (pw2 i) (Nat.mul (nat_lit 9) i)

@[expose] noncomputable def matW (M : Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) mId
    (fun c _ ih => strictN ih fun ih =>
      mcomp (fget M (Nat.add (nat_lit 3) (Nat.shiftRight c (nat_lit 1))) (nat_lit 81)) ih) w

@[expose] noncomputable def mtList (M : Nat) (W : List (List Nat)) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun w _ ih i => strictN (matW M w) fun X =>
      Nat.lor (Nat.shiftLeft X (Nat.mul (nat_lit 81) i)) (ih (Nat.succ i))) W (nat_lit 0)

@[expose] noncomputable def mt (MT t : Nat) : Nat := fget MT t (nat_lit 81)

@[expose] noncomputable def evenW (W : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun w _ ih => andB (List.rec (motive := fun _ => Bool) true
      (fun c _ ih' => andB (Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0)) ih') w) ih) W

@[expose] noncomputable def check3010T (A Tg TE FA : Nat) : Bool :=
  strictB (keysK TE) fun KY =>
    andB (Nat.beq (elt TE (nat_lit 0)) ID693)
      (andB (allN (nat_lit 64) fun i => allN (nat_lit 64) fun j =>
          orB (Nat.beq i j) (notB (Nat.beq (fget KY i (nat_lit 20)) (fget KY j (nat_lit 20)))))
        (andB (allN (nat_lit 64) fun i => allN (nat_lit 4) fun g =>
            strictB (pc (elt Tg g) (elt TE i)) fun x => strictB (idxK KY (keyP x)) fun j =>
              andB (Nat.blt j (nat_lit 64)) (Nat.beq (elt TE j) x))
          (andB (allN (nat_lit 4) fun g => strictB (elt Tg g) fun t => Nat.beq (pc t t) ID693)
            (andB (allN (nat_lit 63) fun j => strictB (elt TE (Nat.succ j)) fun x =>
                notB (allBelow (nat_lit 693) (nat_lit 11) fun p =>
                  orB (Nat.beq (fget FA p (nat_lit 1)) (nat_lit 0)) (Nat.beq (ap10 x p) p)))
              (allN (nat_lit 9) fun i => strictB (elt A i) fun a =>
                allBelow (nat_lit 693) (nat_lit 11) fun p =>
                  orB (Nat.beq (fget FA p (nat_lit 1)) (nat_lit 0)) (Nat.beq (ap10 a p) p))))))

@[expose] noncomputable def fixV (X : Nat) : Nat :=
  sumBelow (nat_lit 512) (nat_lit 8) fun v => nIf(Nat.beq (mapV X v) v, nat_lit 1, nat_lit 0)

@[expose] noncomputable def fixV2 (X Y : Nat) : Nat :=
  sumBelow (nat_lit 512) (nat_lit 8) fun v =>
    nIf(andB (Nat.beq (mapV X v) v) (Nat.beq (mapV Y v) v), nat_lit 1, nat_lit 0)

@[expose] noncomputable def commGens (MU TG x : Nat) : Bool :=
  allN (nat_lit 4) fun g => strictB (fget TG g (nat_lit 7)) fun t => Nat.beq (mu MU x t) (mu MU t x)

@[expose] noncomputable def thomK (MU MT TG : Nat) : Bool :=
  andB (allN (nat_lit 64) fun x => orB (commGens MU TG x)
      (Nat.ble (sumN (nat_lit 64) fun y =>
        nIf(Nat.beq (mu MU y x) (mu MU x y), nat_lit 1, nat_lit 0)) (nat_lit 16)))
    (andB (Nat.ble (sumN (nat_lit 64) fun x => nIf(commGens MU TG x, nat_lit 1, nat_lit 0))
        (nat_lit 16))
      (andB (allN (nat_lit 64) fun x => orB (Nat.beq x (nat_lit 0))
          (Nat.ble (fixV (mt MT x)) (nat_lit 32)))
        (andB (allN (nat_lit 64) fun x => orB (Nat.beq (mu MU x x) (nat_lit 0))
            (Nat.ble (fixV (mt MT x)) (nat_lit 16)))
          (allN (nat_lit 64) fun b => allN (nat_lit 64) fun c =>
            orB (Nat.beq b c) (orB (Nat.beq b (nat_lit 0)) (orB (Nat.beq c (nat_lit 0))
              (orB (notB (Nat.beq (mu MU b b) (nat_lit 0)))
                (orB (notB (Nat.beq (mu MU c c) (nat_lit 0)))
                  (orB (notB (Nat.beq (mu MU b c) (mu MU c b)))
                    (Nat.ble (fixV2 (mt MT b) (mt MT c)) (nat_lit 16)))))))))))

@[expose] noncomputable def imgE (MU MT TG k e : Nat) : Nat :=
  strictN (Nat.shiftRight e (nat_lit 9)) fun t => strictN (Nat.land e (nat_lit 511)) fun v =>
    nIf(Nat.blt k (nat_lit 9),
      Nat.add (Nat.mul t (nat_lit 512))
        (Nat.xor v (Nat.xor (pw2 k) (mapV (mt MT t) (pw2 k)))),
      strictN (fget TG (Nat.sub k (nat_lit 9)) (nat_lit 7)) fun g =>
        Nat.add (Nat.mul (mu MU (mu MU g t) g) (nat_lit 512)) (mapV (mt MT g) v))

@[expose] noncomputable def isInvE (MU MT e : Nat) : Bool :=
  strictB (Nat.shiftRight e (nat_lit 9)) fun t =>
    andB (notB (Nat.beq e (nat_lit 0)))
      (andB (Nat.beq (mu MU t t) (nat_lit 0))
        (Nat.beq (mapV (mt MT t) (Nat.land e (nat_lit 511))) (Nat.land e (nat_lit 511))))

@[expose] noncomputable def invSet (MU MT : Nat) : Nat :=
  sumBelow (nat_lit 32768) (nat_lit 512) fun e => nIf(isInvE MU MT e, pw2 e, nat_lit 0)

abbrev BState : Type := Nat × List Nat × Nat

@[expose] noncomputable def strictS (y : Nat) (k : Nat → BState) : BState :=
  Nat.rec (motive := fun _ => BState) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def bfsStep (MU MT TG : Nat) (st : BState) : BState :=
  List.rec (motive := fun _ => BState) st
    (fun e q _ => Nat.rec (motive := fun _ => BState) (st.1, q, st.2.2)
      (fun k acc => strictS (imgE MU MT TG k e) fun x =>
        Bool.rec (motive := fun _ => BState) (Nat.lor acc.1 (pw2 x), x :: acc.2.1, Nat.succ acc.2.2)
          acc (Nat.beq (fget acc.1 x (nat_lit 1)) (nat_lit 1)))
      (nat_lit 13))
    st.2.1

@[expose] noncomputable def classE (MU MT TG e : Nat) : BState :=
  Nat.rec (motive := fun _ => BState) (pw2 e, [e], nat_lit 1)
    (fun _ st => strictS st.1 fun _ => bfsStep MU MT TG st) (nat_lit 65)

@[expose] noncomputable def doneSet (st : BState) : Nat :=
  List.rec (motive := fun _ => Nat) st.1 (fun _ _ _ => nat_lit 0) st.2.1

@[expose] noncomputable def sbarK (MU MT TG RD FX n : Nat) : Bool :=
  strictB (invSet MU MT) fun I =>
    andB (Nat.beq I (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
        (fun r acc => strictN acc fun acc =>
          Nat.lor acc (doneSet (classE MU MT TG (fget RD r (nat_lit 15))))) n))
      (andB (allN n fun r => strictB (classE MU MT TG (fget RD r (nat_lit 15))).2.2 fun s =>
          andB (orB (notB (Nat.beq (fget FX r (nat_lit 10)) (nat_lit 53))) (Nat.ble (nat_lit 2) s))
            (orB (notB (Nat.beq (fget FX r (nat_lit 10)) (nat_lit 21))) (Nat.ble (nat_lit 8) s)))
        (allBelow (nat_lit 32768) (nat_lit 512) fun e =>
          orB (Nat.ble e (nat_lit 1))
            (notB (allN (nat_lit 13) fun k => Nat.beq (imgE MU MT TG k e) e))))

end CFSG.KC.U6

end
