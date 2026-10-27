module

public import Certificates.Data.Kernel.TcRes.C2Plane

public section

namespace CFSG.TcRes.TK

@[expose] noncomputable def pos8OK (V POS g : Nat) : Bool :=
  strictB (fld V (nat_lit 128) g) fun vg =>
    Bool.rec (motive := fun _ => Bool) (notB (bit POS g)) (bit POS g)
      (allLt (nat_lit 8) fun m => Nat.ble (nat_lit 7) (fld vg (nat_lit 16) m))

@[expose] noncomputable def squash16 (x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i ih => strictN ih fun a => Nat.lor a (Nat.shiftLeft
      (Nat.land (Nat.shiftRight (Nat.mul (fld x (nat_lit 64) i) (nat_lit 281483566907400))
        (nat_lit 48)) (nat_lit 15)) (Nat.mul (nat_lit 4) i)))
    (nat_lit 60)

@[expose] noncomputable def posL (QS : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) LOW16
    (fun m ih => strictN ih fun a =>
      Nat.land a (Nat.land (Nat.shiftRight (Nat.add (QS m) (Nat.mul (nat_lit 9) LOW16)) (nat_lit 4))
        LOW16)) (nat_lit 8)

@[expose] noncomputable def dec8OK (QS MVS : Nat → Nat) (V POS DEC g : Nat) : Bool :=
  strictB (fld V (nat_lit 128) g) fun vg =>
  strictB (Nat.rec (motive := fun _ => Nat) LOW16
    (fun m ih => strictN ih fun a =>
      Nat.land a (Nat.land (Nat.shiftRight (Nat.sub (Nat.mul (Nat.add (fld vg (nat_lit 16) m) (nat_lit 16))
        LOW16) (QS m)) (nat_lit 4)) LOW16)) (nat_lit 8)) fun gd =>
    andB (Nat.beq (squash16 (posL QS)) POS)
      (Nat.beq (fld DEC (nat_lit 240) g)
        (squash16 (Nat.land (posL QS) (Nat.land (fld (MVS g) (nat_lit 3840) (nat_lit 3)) gd))))

@[expose] noncomputable def treeM8 (ADJ Φ c : Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat)
    (fun _ C NB => strictN (Nat.land NB Φ) fun A =>
      Bool.rec (motive := fun _ => Nat) (Nat.shiftLeft (nat_lit 1) (nat_lit 240)) C
        (andB (Nat.blt (nat_lit 0) C) (Nat.beq (Nat.land A C) A)))
    (fun _ ih rest C NB =>
      strictN (Nat.land rest (nat_lit 255)) fun g =>
      strictN (Nat.land (Nat.shiftRight rest (nat_lit 8)) (nat_lit 255)) fun pa =>
      strictN (fld ADJ (nat_lit 240) g) fun ag =>
        Bool.rec (motive := fun _ => Nat) (Nat.shiftLeft (nat_lit 1) (nat_lit 240))
          (ih (Nat.shiftRight rest (nat_lit 16)) (Nat.lor C (Nat.shiftLeft (nat_lit 1) g))
            (Nat.lor NB ag))
          (andB (bit Φ g) (andB (notB (bit C g))
            (Bool.rec (motive := fun _ => Bool) (andB (notB (Nat.beq g pa)) (andB (bit C pa)
                (bit ag pa)))
              (Nat.beq g pa) (Nat.beq C (nat_lit 0)))))) c

@[expose] noncomputable def simpN8 (POS DEC psi c : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun _ ih rest acc => strictN (Nat.land rest (nat_lit 255)) fun g =>
      ih (Nat.shiftRight rest (nat_lit 16))
        (Bool.rec (motive := fun _ => Nat) acc (Nat.succ acc)
          (andB (bit POS g) (Nat.beq (Nat.land (fld DEC (nat_lit 240) g) psi) (nat_lit 0))))) c

@[expose] noncomputable def ksOf (r N : Nat) : Nat :=
  Nat.add (nat_lit 1) (Nat.add (Nat.mul (nat_lit 2) (b2n (famA r N)))
    (Nat.add (Nat.mul (nat_lit 4) (b2n (famD r N)))
      (Nat.mul (nat_lit 8) (b2n (orB (famE r N) (famD4 r N))))))

@[expose] noncomputable def crK8 (ADJ POS DEC : Nat) (ph : Nat → Nat) (cr Φ g0 : Nat)
    (k : Nat → Nat → Bool) : Bool :=
  strictB (Nat.land cr (nat_lit 127)) fun c =>
  strictB (Nat.shiftRight cr (nat_lit 15)) fun rest =>
  strictB (treeM8 ADJ Φ c rest (nat_lit 0) (nat_lit 0)) fun psi =>
  strictB (olen ph psi (nat_lit 12) (Nat.land rest (nat_lit 255)) (nat_lit 1)) fun e =>
  strictB (simpN8 POS DEC psi c rest (nat_lit 0)) fun r =>
    andB (Nat.blt psi (Nat.shiftLeft (nat_lit 1) (nat_lit 240))) (andB (bit psi g0)
      (andB (Nat.blt (nat_lit 0) e)
        (k psi (Nat.add e (Nat.add (Nat.mul (nat_lit 16) r) (Nat.add (Nat.mul (nat_lit 256) c)
          (Nat.mul (nat_lit 65536) (ksOf r c))))))))

@[expose] noncomputable def mP (p n : Nat) : Bool :=
  Nat.beq (Nat.mod (Nat.sub (Nat.pow (nat_lit 2) n) (nat_lit 1)) p) (nat_lit 0)

@[expose] noncomputable def pP (p n : Nat) : Bool :=
  Nat.beq (Nat.mod (Nat.add (Nat.pow (nat_lit 2) n) (nat_lit 1)) p) (nat_lit 0)

@[expose] noncomputable def splitP (p l : Nat) : Bool :=
  strictB (Nat.land l (nat_lit 15)) fun t =>
  strictB (Nat.shiftRight l (nat_lit 8)) fun n =>
    orB (andB (untw t) (mP p n)) (orB (andB (notB (untw t)) (andB (notB (Nat.beq t (nat_lit 8))) (pP p n)))
      (orB (andB (orB (Nat.beq t (nat_lit 3)) (Nat.beq t (nat_lit 8))) (mP p n))
        (andB (Nat.beq n (nat_lit 1)) (Nat.beq p (nat_lit 3)))))

@[expose] noncomputable def halfP (p l : Nat) : Bool :=
  strictB (Nat.land l (nat_lit 15)) fun t =>
  strictB (Nat.land (Nat.shiftRight l (nat_lit 4)) (nat_lit 15)) fun r =>
  strictB (Nat.shiftRight l (nat_lit 8)) fun n =>
    orB (splitP p l) (orB (andB (orB (Nat.beq t (nat_lit 2)) (orB (Nat.beq t (nat_lit 5))
      (Nat.beq t (nat_lit 6)))) (pP p n))
    (orB (andB (orB (andB (Nat.beq t (nat_lit 1)) (Nat.beq r (nat_lit 5))) (Nat.beq t (nat_lit 7))) (mP p n))
    (orB (andB (Nat.beq t (nat_lit 0)) (andB (Nat.beq r (nat_lit 5)) (andB (Nat.beq n (nat_lit 2))
        (Nat.beq p (nat_lit 5)))))
    (orB (andB (Nat.beq t (nat_lit 0)) (andB (Nat.beq r (nat_lit 8)) (andB (Nat.beq n (nat_lit 1))
        (Nat.beq p (nat_lit 7)))))
      (andB (Nat.beq t (nat_lit 4)) (andB (Nat.beq n (nat_lit 1)) (Nat.beq p (nat_lit 7))))))))

@[expose] noncomputable def dKs (d : Nat) : Nat := Nat.shiftRight d (nat_lit 16)

@[expose] noncomputable def labK (d k f : Nat) : Nat :=
  compLab (dR d) (Nat.land (Nat.shiftRight d (nat_lit 8)) (nat_lit 255)) k (Nat.mul (dE d) f)

@[expose] noncomputable def anyLabK (q : Nat → Bool) (d f : Nat) : Bool :=
  anyLt (nat_lit 4) fun k => andB (bit (dKs d) k) (anyLab q (labK d k f))

@[expose] noncomputable def meetsK (a b f : Nat) : Bool :=
  anyLt (nat_lit 4) fun k => andB (bit (dKs a) k)
    (anyLt (nat_lit 4) fun k' => andB (bit (dKs b) k') (meets (labK a k f) (labK b k' f)))

@[expose] noncomputable def flags5 (d : Nat) : Nat :=
  Nat.add (b2n (anyLabK (splitP (nat_lit 5)) d (nat_lit 1)))
  (Nat.add (Nat.mul (nat_lit 2) (b2n (anyLabK (halfP (nat_lit 5)) d (nat_lit 1))))
  (Nat.add (Nat.mul (nat_lit 4) (b2n (anyLabK (splitP (nat_lit 5)) d (nat_lit 3))))
  (Nat.add (Nat.mul (nat_lit 8) (b2n (anyLabK (halfP (nat_lit 5)) d (nat_lit 3))))
  (Nat.add (Nat.mul (nat_lit 16) (b2n (anyLabK (splitP (nat_lit 5)) d (nat_lit 5))))
    (Nat.mul (nat_lit 32) (b2n (anyLabK (halfP (nat_lit 5)) d (nat_lit 5))))))))

@[expose] noncomputable def jok5X (f fi psJ dJ : Nat) (ps ds fs : Nat → Nat) (x : Nat) : Bool :=
  notB (andB (notB (Nat.beq (ps x) psJ)) (andB (bit (fs x) (Nat.mul (nat_lit 2) fi))
    (allLt (nat_lit 6) fun y => orB (Nat.beq y x)
      (orB (bit (fs y) (Nat.succ (Nat.mul (nat_lit 2) fi))) (meetsK (ds y) dJ f)))))

@[expose] noncomputable def jok5 (s psJ dJ : Nat) (ps ds fs : Nat → Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (andB (allLt (nat_lit 6) (jok5X (nat_lit 1) (nat_lit 0) psJ dJ ps ds fs))
      (allLt (nat_lit 6) (jok5X (nat_lit 5) (nat_lit 2) psJ dJ ps ds fs)))
    (allLt (nat_lit 6) (jok5X (nat_lit 3) (nat_lit 1) psJ dJ ps ds fs))
    (Nat.beq s (nat_lit 1))

@[expose] noncomputable def kv8 (RC : Nat → Nat) (B x : Nat) : Nat := squash8 (zl5 (dot8 RC B x))

@[expose] noncomputable def line8OK (ADJ POS DEC PW : Nat) (RC BS : Nat → Nat) (E : Nat) : Bool :=
  strictB (Nat.shiftRight E (nat_lit 288)) fun cr =>
    crK8 ADJ POS DEC (fun g => fld PW (nat_lit 8) g) cr
      (kv8 RC (BS (Nat.land E (nat_lit 1))) (Nat.land (Nat.shiftRight E (nat_lit 1)) (nat_lit 1023)))
      (Nat.land (Nat.shiftRight cr (nat_lit 15)) (nat_lit 255))
      fun p d => andB (Nat.beq p (Nat.land (Nat.shiftRight E (nat_lit 35)) M240))
        (andB (Nat.beq d (Nat.land (Nat.shiftRight E (nat_lit 11)) (nat_lit 16777215)))
          (Nat.beq (flags5 d) (Nat.land (Nat.shiftRight E (nat_lit 275)) (nat_lit 63))))

@[expose] noncomputable def lin5 (c1 c2 a : Nat) : Nat :=
  sumLt (nat_lit 4) fun i => Nat.mul (Nat.pow (nat_lit 5) i)
    (Nat.mod (Nat.add (Nat.mul a (dg5 c1 i)) (dg5 c2 i)) (nat_lit 5))

@[expose] noncomputable def leK8 (LS : Nat → Nat) (s g0 blk j x : Nat)
    (k : Nat → Nat → Nat → Bool) : Bool :=
  strictB (LS (fld (Nat.shiftRight blk (nat_lit 128)) (nat_lit 12) j)) fun E =>
  strictB (Nat.land (Nat.shiftRight E (nat_lit 35)) M240) fun p =>
    andB (Nat.beq (Nat.land E (nat_lit 1)) s)
      (andB (Nat.beq (Nat.land (Nat.shiftRight E (nat_lit 1)) (nat_lit 1023)) x)
        (andB (bit p g0) (k p (Nat.land (Nat.shiftRight E (nat_lit 11)) (nat_lit 16777215))
          (Nat.land (Nat.shiftRight E (nat_lit 275)) (nat_lit 63)))))

@[expose] noncomputable def sel6 (a b c d e f i : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (sel4 c d e f (Nat.sub i (nat_lit 2)))
    (Bool.rec (motive := fun _ => Nat) b a (Nat.beq i (nat_lit 0))) (Nat.blt i (nat_lit 2))

@[expose] noncomputable def jb8OK (ADJ POS DEC : Nat) (ph LS : Nat → Nat)
    (s P c1 c2 C g0 blk : Nat) : Bool :=
  crK8 ADJ POS DEC ph (Nat.land blk (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 128)) (nat_lit 1)))
    P g0 fun psJ dJ =>
  andB (Nat.beq psJ C) (andB (Nat.ble (nat_lit 2) (dE dJ))
  (leK8 LS s g0 blk (nat_lit 0) c1 fun p0 d0 f0 =>
  leK8 LS s g0 blk (nat_lit 1) (lin5 c1 c2 (nat_lit 0)) fun p1 d1 f1 =>
  leK8 LS s g0 blk (nat_lit 2) (lin5 c1 c2 (nat_lit 1)) fun p2 d2 f2 =>
  leK8 LS s g0 blk (nat_lit 3) (lin5 c1 c2 (nat_lit 2)) fun p3 d3 f3 =>
  leK8 LS s g0 blk (nat_lit 4) (lin5 c1 c2 (nat_lit 3)) fun p4 d4 f4 =>
  leK8 LS s g0 blk (nat_lit 5) (lin5 c1 c2 (nat_lit 4)) fun p5 d5 f5 =>
    jok5 s psJ dJ (sel6 p0 p1 p2 p3 p4 p5) (sel6 d0 d1 d2 d3 d4 d5) (sel6 f0 f1 f2 f3 f4 f5)))

@[expose] noncomputable def compEnd8 (ADJ POS DEC : Nat) (ph LS : Nat → Nat)
    (s P c1 c2 A C rt i : Nat) (k : Nat → Bool) : Bool :=
  strictB (olen ph C (nat_lit 12) rt (nat_lit 1)) fun e =>
    andB (Nat.blt (nat_lit 0) e)
      (Bool.rec (motive := fun _ => Bool)
        (andB (jb8OK ADJ POS DEC ph LS s P c1 c2 C rt
            (fld (Nat.shiftRight A (nat_lit 8)) (nat_lit 208) i))
          (k (Nat.succ i)))
        (k i) (Nat.beq e (nat_lit 1)))

@[expose] noncomputable def aWalk8 (ADJ POS DEC : Nat) (ph LS : Nat → Nat)
    (s P c1 c2 A c : Nat) : Nat → Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → Bool)
    (fun _ C rt i => compEnd8 ADJ POS DEC ph LS s P c1 c2 A C rt i fun j =>
      Nat.beq j (Nat.land A (nat_lit 255)))
    (fun _ ih rest C rt i =>
      strictB (Nat.land rest (nat_lit 255)) fun g =>
      strictB (Nat.shiftLeft (nat_lit 1) g) fun bg =>
        Bool.rec (motive := fun _ => Bool)
          (ih (Nat.shiftRight rest (nat_lit 16)) (Nat.lor C bg) rt i)
          (Bool.rec (motive := fun _ => Bool)
            (compEnd8 ADJ POS DEC ph LS s P c1 c2 A C rt i fun j =>
              ih (Nat.shiftRight rest (nat_lit 16)) bg g j)
            (ih (Nat.shiftRight rest (nat_lit 16)) bg g i)
            (Nat.beq C (nat_lit 0)))
          (Nat.beq g (Nat.land (Nat.shiftRight rest (nat_lit 8)) (nat_lit 255)))) c

@[expose] noncomputable def ana8OK (ADJ POS DEC PW : Nat) (RC BS LS : Nat → Nat) (e A : Nat) :
    Bool :=
  strictB (Nat.land e (nat_lit 1023)) fun c1 =>
  strictB (Nat.land (Nat.shiftRight e (nat_lit 10)) (nat_lit 1023)) fun c2 =>
  strictB (Nat.land (Nat.shiftRight e (nat_lit 20)) (nat_lit 1)) fun s =>
  strictB (kmask5 RC (BS s) c1 c2) fun P =>
    aWalk8 ADJ POS DEC (fun g => fld PW (nat_lit 8) g) LS s P c1 c2 A
      (Nat.land (Nat.shiftRight e (nat_lit 34)) (nat_lit 63)) (Nat.shiftRight e (nat_lit 40))
      (nat_lit 0) (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def mleaf8 (ADJ POS DEC PW : Nat) (RC BS LS LF AS : Nat → Nat) (L : Nat) :
    Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ ih p rest =>
      strictB (Nat.land rest M448) fun e =>
      andB (orB (Nat.ble (nat_lit 1612) p) (orB (Nat.beq (Nat.land (Nat.shiftRight e (nat_lit 21))
          (nat_lit 1)) (nat_lit 0))
        (ana8OK ADJ POS DEC PW RC BS LS e (AS (Nat.land (Nat.shiftRight e (nat_lit 22))
          (nat_lit 4095))))))
        (ih (Nat.succ p) (Nat.shiftRight rest (nat_lit 448))))
    (nat_lit 16) (Nat.mul L (nat_lit 16)) (LF L)

end CFSG.TcRes.TK

end
