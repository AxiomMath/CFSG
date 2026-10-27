module

public import Certificates.Data.Kernel.TcRes.C2Moved

public section

namespace CFSG.TcRes.TK

@[expose] noncomputable def isoOK (X Y t : Nat) : Bool :=
  allLt (nat_lit 8) fun a => strictB (fld t (nat_lit 8) a) fun ta =>
    andB (Nat.blt ta (nat_lit 240)) <| allLt (nat_lit 8) fun b =>
      Nat.beq (ipK8 X Y ta (fld t (nat_lit 8) b)) (ipK8 X Y a b)

@[expose] noncomputable def commOK (PW PG : Nat) : Bool :=
  allLt (nat_lit 240) fun g =>
    Nat.beq (fld PG (nat_lit 8) (fld PW (nat_lit 8) g)) (fld PW (nat_lit 8) (fld PG (nat_lit 8) g))

@[expose] noncomputable def genOK (RTs : Nat → Nat) (X Y PAR PW t PG : Nat) : Bool :=
  andB (isoOK X Y t) (andB (pw8OK RTs t PAR PG) (commOK PW PG))

@[expose] noncomputable def zlOK (MVS : Nat → Nat) (PW ZL : Nat) : Bool :=
  allLt (nat_lit 240) fun b =>
    Nat.beq (fld ZL (nat_lit 16) b) (fld (mvf MVS (fld PW (nat_lit 8) b) (nat_lit 2)) (nat_lit 16) b)

@[expose] noncomputable def pop240 (x : Nat) : Nat := fld (Nat.mul x LOW16) (nat_lit 16) (nat_lit 239)

@[expose] noncomputable def bmask (MVS : Nat → Nat) (PW ZL a : Nat) : Nat :=
  Nat.land (mvf MVS a (nat_lit 1)) (Nat.land (mvf MVS (fld PW (nat_lit 8) a) (nat_lit 2)) ZL)

@[expose] noncomputable def cntOK (MVS : Nat → Nat) (PW ZL : Nat) : Bool :=
  Nat.beq (sumLt (nat_lit 240) fun a => Nat.mul (fld ZL (nat_lit 16) a) (pop240 (bmask MVS PW ZL a)))
    (nat_lit 7680)

@[expose] noncomputable def M40 : Nat := nat_lit 1099511627775

@[expose] noncomputable def trec (LF : Nat → Nat) (p : Nat) : Nat :=
  Nat.land (Nat.shiftRight (LF (Nat.shiftRight p (nat_lit 6))) (Nat.mul (Nat.land p (nat_lit 63)) (nat_lit 40)))
    M40

@[expose] noncomputable def tparOK (PGs : Nat → Nat) (a b d k pe : Nat) : Bool :=
  andB (Nat.beq (Nat.succ (Nat.land (Nat.shiftRight pe (nat_lit 16)) (nat_lit 63))) d)
    (andB (Nat.blt k (nat_lit 3)) (strictB (PGs k) fun pg =>
      andB (Nat.beq (fld pg (nat_lit 8) (Nat.land (Nat.shiftRight pe (nat_lit 8)) (nat_lit 255))) a)
        (Nat.beq (fld pg (nat_lit 8) (Nat.land pe (nat_lit 255))) b)))

@[expose] noncomputable def trecOK (PGs LF : Nat → Nat) (a0 b0 e a b : Nat) : Bool :=
  strictB (Nat.land (Nat.shiftRight e (nat_lit 16)) (nat_lit 63)) fun d =>
  strictB (Nat.land (Nat.shiftRight e (nat_lit 22)) (nat_lit 8191)) fun p =>
    Bool.rec (motive := fun _ => Bool)
      (andB (Nat.blt p (nat_lit 7680))
        (strictB (trec LF p) (tparOK PGs a b d (Nat.shiftRight e (nat_lit 35)))))
      (andB (Nat.beq a a0) (Nat.beq b b0))
      (Nat.beq d (nat_lit 0))

@[expose] noncomputable def tWalk (MVS PGs LF : Nat → Nat) (PW ZL a0 b0 c : Nat) :
    Nat → Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → Bool) (fun _ _ _ _ => true)
    (fun _ ih rest prev ca cm =>
      strictB (Nat.land rest M40) fun e =>
      strictB (Nat.land e (nat_lit 65535)) fun key =>
      strictB (Nat.land e (nat_lit 255)) fun b =>
      strictB (Nat.shiftRight key (nat_lit 8)) fun a =>
      strictB (Bool.rec (motive := fun _ => Nat) (bmask MVS PW ZL a) cm (Nat.beq a ca)) fun m =>
        andB (Nat.blt prev key) (andB (Nat.beq (fld ZL (nat_lit 16) a) (nat_lit 1))
          (andB (bit m (Nat.mul (nat_lit 16) b)) (andB (trecOK PGs LF a0 b0 e a b)
            (ih (Nat.shiftRight rest (nat_lit 40)) key a m))))) c

@[expose] noncomputable def tprev (LF : Nat → Nat) (L : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun l _ => Nat.land (trec LF (Nat.add (Nat.mul l (nat_lit 64)) (nat_lit 63))) (nat_lit 65535)) L

@[expose] noncomputable def tleaf (MVS PGs LF : Nat → Nat) (PW ZL a0 b0 L : Nat) : Bool :=
  tWalk MVS PGs LF PW ZL a0 b0 (nat_lit 64) (LF L) (tprev LF L) (nat_lit 256) (nat_lit 0)

@[expose] noncomputable def rco (V g m : Nat) : Nat :=
  spk (fld (fld V (nat_lit 128) g) (nat_lit 16) m) (nat_lit 7)

@[expose] noncomputable def xe (XM i k : Nat) : Nat :=
  spk (fld XM (nat_lit 8) (Nat.add (Nat.mul (nat_lit 8) i) k)) (nat_lit 128)

@[expose] noncomputable def sabs (x : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Nat.sub OFS x) (Nat.sub x OFS) (Nat.ble OFS x)

@[expose] noncomputable def smoothN (n : Nat) : Bool :=
  andB (Nat.blt (nat_lit 0) n)
    (Nat.beq (Nat.mod (Nat.pow (nat_lit 30) (nat_lit 64)) n) (nat_lit 0))

@[expose] noncomputable def colsOK (PW COLS : Nat) : Bool :=
  andB (allLt (nat_lit 8) fun k => Nat.blt (fld COLS (nat_lit 8) k) (nat_lit 240)) <|
  allLt (nat_lit 4) fun i =>
    Nat.beq (fld COLS (nat_lit 8) (Nat.succ (Nat.mul (nat_lit 2) i)))
      (fld PW (nat_lit 8) (fld COLS (nat_lit 8) (Nat.mul (nat_lit 2) i)))

@[expose] noncomputable def bxOK (V COLS XM DD : Nat) : Bool :=
  strictB (spk DD (nat_lit 128)) fun dc =>
    andB (notB (Nat.beq dc OFS)) (andB (smoothN (sabs dc))
      (allLt (nat_lit 8) fun i => allLt (nat_lit 8) fun j =>
        Nat.beq (ssum (nat_lit 8) fun k =>
            smul (rco V (fld COLS (nat_lit 8) k) i) (xe XM k j))
          (Bool.rec (motive := fun _ => Nat) OFS dc (Nat.beq i j))))

@[expose] noncomputable def yv (V XM e i : Nat) : Nat :=
  ssum (nat_lit 8) fun k => smul (xe XM i k) (rco V e k)

@[expose] noncomputable def wK (V XM e : Nat) (k : Nat → Nat → Nat → Nat → Bool) : Bool :=
  strictB (yv V XM e (nat_lit 4)) fun y4 =>
  strictB (yv V XM e (nat_lit 5)) fun y5 =>
  strictB (yv V XM e (nat_lit 6)) fun y6 =>
  strictB (yv V XM e (nat_lit 7)) fun y7 => k y4 y5 y6 y7

@[expose] noncomputable def crossK (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) (k : Nat → Nat → Bool) : Bool :=
  strictB (sadd (sadd (smul a0 b2) (sneg (smul a1 b3))) (sneg (sadd (smul a2 b0) (sneg (smul a3 b1)))))
    fun re =>
  strictB (sadd (sadd (smul a0 b3) (smul a1 b2)) (sneg (sadd (smul a2 b1) (smul a3 b0)))) fun im =>
    k re im

@[expose] noncomputable def gnorm (x y : Nat) : Nat :=
  Nat.add (Nat.mul (sabs x) (sabs x)) (Nat.mul (sabs y) (sabs y))

@[expose] noncomputable def gz (x y : Nat) : Bool := andB (Nat.beq x OFS) (Nat.beq y OFS)

@[expose] noncomputable def gsm (x y : Nat) : Bool := andB (notB (gz x y)) (smoothN (gnorm x y))

@[expose] noncomputable def pbE (CMs : Nat → Nat) (V XM SG KE REPS e : Nat) : Bool :=
  wK V XM e fun y4 y5 y6 y7 =>
    Bool.rec (motive := fun _ => Bool)
      (andB (notB (bit SG e)) (andB (orB (gsm y4 y5) (gsm y6 y7))
        (strictB (fld KE (nat_lit 4) e) fun k =>
          andB (Nat.blt k (nat_lit 12)) (andB (bit (CMs k) e)
            (strictB (fld REPS (nat_lit 8) k) fun r =>
              andB (Nat.ble r e) (wK V XM r fun z4 z5 z6 z7 =>
                crossK y4 y5 y6 y7 z4 z5 z6 z7 gz))))))
      (bit SG e)
      (andB (gz y4 y5) (gz y6 y7))

@[expose] noncomputable def pbW (CMs : Nat → Nat) (V XM SG KE REPS i : Nat) : Bool :=
  allLt (nat_lit 60) fun j => pbE CMs V XM SG KE REPS (Nat.add (Nat.mul (nat_lit 60) i) j)

@[expose] noncomputable def sMask (RTs : Nat → Nat) (NEG a b : Nat) : Nat :=
  strictN (fld (RTs b) (nat_lit 8) a) fun c =>
    Nat.lor (Nat.shiftLeft (nat_lit 1) a) (Nat.lor (Nat.shiftLeft (nat_lit 1) b)
      (Nat.lor (Nat.shiftLeft (nat_lit 1) c) (Nat.lor (Nat.shiftLeft (nat_lit 1) (fld NEG (nat_lit 8) a))
        (Nat.lor (Nat.shiftLeft (nat_lit 1) (fld NEG (nat_lit 8) b))
          (Nat.shiftLeft (nat_lit 1) (fld NEG (nat_lit 8) c))))))

@[expose] noncomputable def sMaskP (RTs : Nat → Nat) (NEG PW a b : Nat) : Nat :=
  strictN (fld (RTs b) (nat_lit 8) a) fun c =>
    Nat.lor (Nat.shiftLeft (nat_lit 1) (fld PW (nat_lit 8) a))
      (Nat.lor (Nat.shiftLeft (nat_lit 1) (fld PW (nat_lit 8) b))
      (Nat.lor (Nat.shiftLeft (nat_lit 1) (fld PW (nat_lit 8) c))
      (Nat.lor (Nat.shiftLeft (nat_lit 1) (fld PW (nat_lit 8) (fld NEG (nat_lit 8) a)))
        (Nat.lor (Nat.shiftLeft (nat_lit 1) (fld PW (nat_lit 8) (fld NEG (nat_lit 8) b)))
          (Nat.shiftLeft (nat_lit 1) (fld PW (nat_lit 8) (fld NEG (nat_lit 8) c)))))))

@[expose] noncomputable def sigOK (RTs : Nat → Nat) (NEG PW COLS SG : Nat) : Bool :=
  strictB (fld COLS (nat_lit 8) (nat_lit 0)) fun a =>
  strictB (fld COLS (nat_lit 8) (nat_lit 2)) fun b =>
    Nat.beq SG (Nat.lor (sMask RTs NEG a b) (sMaskP RTs NEG PW a b))

@[expose] noncomputable def lorLt (c : Nat) (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun i ih => strictN ih fun a => Nat.lor a (f i)) c

@[expose] noncomputable def clsOK (CMs : Nat → Nat) (V XM SG REPS : Nat) : Bool :=
  strictB (Nat.xor M240 SG) fun U =>
    andB (Nat.beq (sumLt (nat_lit 12) CMs) U) (andB (Nat.beq (lorLt (nat_lit 12) CMs) U)
    (andB (allLt (nat_lit 12) fun k => bit (CMs k) (fld REPS (nat_lit 8) k))
    (andB (allLt (nat_lit 11) fun k =>
        Nat.blt (fld REPS (nat_lit 8) k) (fld REPS (nat_lit 8) (Nat.succ k)))
      (allLt (nat_lit 12) fun i => allLt (nat_lit 12) fun j => orB (Nat.ble j i)
        (wK V XM (fld REPS (nat_lit 8) i) fun a4 a5 a6 a7 =>
          wK V XM (fld REPS (nat_lit 8) j) fun b4 b5 b6 b7 =>
            crossK a4 a5 a6 a7 b4 b5 b6 b7 gsm)))))

@[expose] noncomputable def lnK (ADJ POS DEC PW cr Φ g0 lp : Nat) : Bool :=
  crK8 ADJ POS DEC (fun g => fld PW (nat_lit 8) g) cr Φ g0 fun psi d =>
    andB (Nat.beq psi (Nat.land lp M240)) (Nat.beq d (Nat.shiftRight lp (nat_lit 240)))

@[expose] noncomputable def lnOK (CMs LCs LPs : Nat → Nat) (ADJ POS DEC PW COLS SG k : Nat) : Bool :=
  lnK ADJ POS DEC PW (LCs k) (Nat.lor SG (CMs k)) (fld COLS (nat_lit 8) (nat_lit 0)) (LPs k)

@[expose] noncomputable def lnJ (RTs LCs LPs : Nat → Nat) (ADJ POS DEC NEG PW COLS SG : Nat) : Bool :=
  strictB (fld COLS (nat_lit 8) (nat_lit 0)) fun a =>
    andB (lnK ADJ POS DEC PW (LCs (nat_lit 12)) SG a (LPs (nat_lit 12)))
      (Nat.beq (Nat.land (LPs (nat_lit 12)) M240) (sMask RTs NEG a (fld COLS (nat_lit 8) (nat_lit 2))))

@[expose] noncomputable def splitF (l : Nat) : Bool :=
  strictB (Nat.land l (nat_lit 15)) fun t =>
  strictB (Nat.mod (Nat.shiftRight l (nat_lit 8)) (nat_lit 4)) fun n4 =>
    orB (andB (untw t) (Nat.beq n4 (nat_lit 0)))
      (orB (andB (notB (untw t)) (andB (notB (Nat.beq t (nat_lit 8))) (Nat.beq n4 (nat_lit 2))))
        (andB (orB (Nat.beq t (nat_lit 3)) (Nat.beq t (nat_lit 8))) (Nat.beq n4 (nat_lit 0))))

@[expose] noncomputable def halfF (l : Nat) : Bool :=
  strictB (Nat.land l (nat_lit 15)) fun t =>
  strictB (Nat.land (Nat.shiftRight l (nat_lit 4)) (nat_lit 15)) fun r =>
  strictB (Nat.mod (Nat.shiftRight l (nat_lit 8)) (nat_lit 4)) fun n4 =>
    orB (splitF l) (orB (andB (orB (Nat.beq t (nat_lit 2)) (orB (Nat.beq t (nat_lit 5))
      (Nat.beq t (nat_lit 6)))) (Nat.beq n4 (nat_lit 2)))
      (andB (orB (andB (Nat.beq t (nat_lit 1)) (Nat.beq r (nat_lit 5))) (Nat.beq t (nat_lit 7)))
        (Nat.beq n4 (nat_lit 0))))

@[expose] noncomputable def jok3X (psJ dJ : Nat) (ps ds : Nat → Nat) (x : Nat) : Bool :=
  notB (andB (notB (Nat.beq (ps x) psJ)) (andB (anyLabK splitF (ds x) (nat_lit 1))
    (allLt (nat_lit 13) fun y => orB (Nat.beq y x)
      (orB (anyLabK halfF (ds y) (nat_lit 1)) (meetsK (ds y) dJ (nat_lit 1))))))

@[expose] noncomputable def jok3 (LPs : Nat → Nat) : Bool :=
  strictB (Nat.land (LPs (nat_lit 12)) M240) fun psJ =>
  strictB (Nat.shiftRight (LPs (nat_lit 12)) (nat_lit 240)) fun dJ =>
    allLt (nat_lit 13)
      (jok3X psJ dJ (fun x => Nat.land (LPs x) M240) (fun x => Nat.shiftRight (LPs x) (nat_lit 240)))

end CFSG.TcRes.TK

end
