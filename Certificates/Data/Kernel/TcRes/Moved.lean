module

public import Certificates.Data.Kernel.TcRes.Plane

public section

namespace CFSG.TcRes.TK

@[expose] noncomputable def OFS : Nat := nat_lit 4294967296

@[expose] noncomputable def spk (a b : Nat) : Nat := Nat.sub (Nat.add OFS a) b

@[expose] noncomputable def smul (x y : Nat) : Nat :=
  Nat.sub (Nat.add (Nat.mul x y) (Nat.add (nat_lit 18446744073709551616) OFS))
    (Nat.mul OFS (Nat.add x y))

@[expose] noncomputable def sadd (x y : Nat) : Nat := Nat.sub (Nat.add x y) OFS

@[expose] noncomputable def sneg (x : Nat) : Nat := Nat.sub (nat_lit 8589934592) x

@[expose] noncomputable def ssum (c : Nat) (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) OFS (fun j ih => strictN ih fun a => sadd (f j) a) c

@[expose] noncomputable def ipK (X Y a b : Nat) : Nat :=
  strictN (Nat.mul (fld X (nat_lit 192) a) (fld Y (nat_lit 192) b)) fun pr =>
    spk (dP (nat_lit 6) pr) (dQ (nat_lit 6) pr)

@[expose] noncomputable def posOK (V POS g : Nat) : Bool :=
  strictB (fld V (nat_lit 96) g) fun vg =>
    Bool.rec (motive := fun _ => Bool) (notB (bit POS g)) (bit POS g)
      (allLt (nat_lit 6) fun m => Nat.ble (nat_lit 7) (fld vg (nat_lit 16) m))

@[expose] noncomputable def decOK (RT X Y POS DEC g : Nat) : Bool :=
  strictB (fld DEC (nat_lit 72) g) fun row =>
  allLt (nat_lit 72) fun d =>
    strictB (ipK X Y g d) fun v =>
    Bool.rec (motive := fun _ => Bool) (notB (bit row d)) (bit row d)
      (andB (bit POS d) (andB (Nat.beq v (Nat.add OFS (nat_lit 1)))
        (bit POS (rtv RT d g))))

@[expose] noncomputable def treeM (ADJ Φ c : Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat)
    (fun _ C NB => strictN (Nat.land NB Φ) fun A =>
      Bool.rec (motive := fun _ => Nat) (Nat.shiftLeft (nat_lit 1) (nat_lit 72)) C
        (andB (Nat.blt (nat_lit 0) C) (Nat.beq (Nat.land A C) A)))
    (fun _ ih rest C NB =>
      strictN (Nat.land rest (nat_lit 127)) fun g =>
      strictN (Nat.land (Nat.shiftRight rest (nat_lit 7)) (nat_lit 127)) fun pa =>
      strictN (fld ADJ (nat_lit 72) g) fun ag =>
        Bool.rec (motive := fun _ => Nat) (Nat.shiftLeft (nat_lit 1) (nat_lit 72))
          (ih (Nat.shiftRight rest (nat_lit 14)) (Nat.lor C (Nat.shiftLeft (nat_lit 1) g))
            (Nat.lor NB ag))
          (andB (bit Φ g) (andB (notB (bit C g))
            (Bool.rec (motive := fun _ => Bool) (andB (notB (Nat.beq g pa)) (andB (bit C pa)
                (bit ag pa)))
              (Nat.beq g pa) (Nat.beq C (nat_lit 0)))))) c

@[expose] noncomputable def olen (ph : Nat → Nat) (psi f : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => nat_lit 0)
    (fun _ ih x s => strictN (ph x) fun y =>
      Bool.rec (motive := fun _ => Nat) (ih y (Nat.succ s)) s (bit psi y)) f

@[expose] noncomputable def phPow (ph : Nat → Nat) (e g : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) g (fun _ ih => strictN ih ph) e

@[expose] noncomputable def simpM (POS DEC psi c : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun _ ih rest acc => strictN (Nat.land rest (nat_lit 127)) fun g =>
      ih (Nat.shiftRight rest (nat_lit 14))
        (Bool.rec (motive := fun _ => Nat) acc
          (Nat.add (Nat.lor acc (Nat.shiftLeft (nat_lit 1) g)) (Nat.shiftLeft (nat_lit 1) (nat_lit 80)))
          (andB (bit POS g) (Nat.beq (Nat.land (fld DEC (nat_lit 72) g) psi) (nat_lit 0))))) c

@[expose] noncomputable def applyW (RT wl : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ v => v)
    (fun _ ih w v => strictN (rtv RT (Nat.land w (nat_lit 127)) v) fun v' =>
      ih (Nat.shiftRight w (nat_lit 7)) v') wl

@[expose] noncomputable def wOK (RT : Nat) (ph : Nat → Nat) (psi c rest e wl w : Nat) : Bool :=
  andB (allLt wl fun i => bit psi (fld w (nat_lit 7) i))
    (Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun _ ih r => strictB (Nat.land r (nat_lit 127)) fun g =>
        andB (Nat.beq (applyW RT wl w (phPow ph e g)) g) (ih (Nat.shiftRight r (nat_lit 14))))
      c rest)

@[expose] noncomputable def adjE (cb j k : Nat) : Nat :=
  strictN (fld cb (nat_lit 8) (Nat.add (nat_lit 85) (Nat.add (Nat.mul (nat_lit 6) j) k))) fun v =>
    spk (Nat.sub v (nat_lit 128)) (Nat.sub (nat_lit 128) v)

@[expose] noncomputable def dlt (cb i : Nat) : Nat := fld (Nat.shiftRight cb (nat_lit 622)) (nat_lit 7) i

@[expose] noncomputable def sDvd (d x : Nat) : Bool := Nat.beq (Nat.mod x d) (Nat.mod OFS d)

@[expose] noncomputable def dltOK (cb r SM : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun i ih prev => strictB (dlt cb i) fun g =>
      andB (Nat.blt g prev) (andB (bit SM g) (ih g))) r (nat_lit 72)

@[expose] noncomputable def odOK (X Y : Nat) (ph : Nat → Nat) (cb r SM c e i i2 : Nat) : Bool :=
  strictB (fld cb (nat_lit 8) (nat_lit 83)) fun dp =>
  strictB (fld cb (nat_lit 8) (nat_lit 84)) fun dn =>
  strictB (Nat.add dp dn) fun d =>
  andB (dltOK cb r SM) (andB (notB (Nat.beq dp dn)) (andB (Nat.blt i r) (andB (Nat.blt i2 r)
  (andB (allLt r fun a => allLt r fun k =>
      Nat.beq (ssum r fun j => smul (ipK X Y (dlt cb a) (dlt cb j)) (adjE cb j k))
        (Bool.rec (motive := fun _ => Nat) OFS (spk dp dn) (Nat.beq a k)))
  (andB (allLt r fun a =>
      Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
        (fun _ ih rest => strictB (Nat.land rest (nat_lit 127)) fun g =>
          andB (sDvd d (ssum r fun j => smul (adjE cb a j) (ipK X Y (dlt cb j) g)))
            (ih (Nat.shiftRight rest (nat_lit 14))))
        c (Nat.shiftRight cb (nat_lit 6)))
    (notB (sDvd (Nat.mul d d) (ssum r fun j => ssum r fun k =>
      smul (smul (adjE cb i2 j) (adjE cb i k))
        (sadd (ipK X Y (dlt cb j) (phPow ph e (dlt cb k)))
          (sneg (ipK X Y (dlt cb j) (dlt cb k))))))))))))

@[expose] noncomputable def famA (r N : Nat) : Bool :=
  andB (Nat.ble (nat_lit 2) r) (Nat.beq N (Nat.mul r (Nat.succ r)))

@[expose] noncomputable def famD (r N : Nat) : Bool :=
  andB (Nat.ble (nat_lit 4) r) (Nat.beq N (Nat.mul (Nat.mul (nat_lit 2) r) (Nat.sub r (nat_lit 1))))

@[expose] noncomputable def famE (r N : Nat) : Bool :=
  andB (Nat.beq r (nat_lit 6)) (Nat.beq N (nat_lit 72))

@[expose] noncomputable def famD4 (r N : Nat) : Bool :=
  andB (Nat.beq r (nat_lit 4)) (Nat.beq N (nat_lit 24))

@[expose] noncomputable def KBAD : Nat := nat_lit 9

@[expose] noncomputable def kindOf (RT X Y : Nat) (ph : Nat → Nat) (cb psi r N SM e : Nat) : Nat :=
  strictN (Nat.land (Nat.shiftRight cb (nat_lit 510)) (nat_lit 7)) fun t =>
  strictN (Nat.land (Nat.shiftRight cb (nat_lit 513)) (nat_lit 15)) fun wl =>
  strictN (Nat.shiftRight cb (nat_lit 517)) fun w =>
  strictN (Nat.land (Nat.shiftRight cb (nat_lit 968)) (nat_lit 7)) fun i1 =>
  strictN (Nat.land (Nat.shiftRight cb (nat_lit 971)) (nat_lit 7)) fun i2 =>
  strictN (Nat.land cb (nat_lit 63)) fun c =>
  strictN (Nat.shiftRight cb (nat_lit 6)) fun rest =>
    Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) KBAD
        (Bool.rec (motive := fun _ => Nat) (nat_lit 0) KBAD
          (orB (famE r N) (orB (famD4 r N) (orB (famD r N) (famA r N)))))
        (Nat.beq t (nat_lit 4)))
      (Bool.rec (motive := fun _ => Nat) KBAD (nat_lit 3)
        (andB (famD4 r N) (andB (odOK X Y ph cb r SM c e i1 i2)
          (odOK X Y ph cb r SM c (Nat.mul (nat_lit 2) e)
            (Nat.land (Nat.shiftRight cb (nat_lit 974)) (nat_lit 7))
            (Nat.land (Nat.shiftRight cb (nat_lit 977)) (nat_lit 7))))))
      (Nat.beq t (nat_lit 3)))
      (Bool.rec (motive := fun _ => Nat) KBAD (nat_lit 2)
        (andB (famD4 r N) (andB (odOK X Y ph cb r SM c e i1 i2)
          (wOK RT ph psi c rest (Nat.mul (nat_lit 2) e) wl w))))
      (Nat.beq t (nat_lit 2)))
      (Bool.rec (motive := fun _ => Nat) KBAD
        (Bool.rec (motive := fun _ => Nat)
          (Bool.rec (motive := fun _ => Nat)
            (Bool.rec (motive := fun _ => Nat)
              (Bool.rec (motive := fun _ => Nat) KBAD (nat_lit 1) (famA r N))
              (nat_lit 2) (famD r N))
            KBAD (famD4 r N))
          (nat_lit 3) (famE r N))
        (odOK X Y ph cb r SM c e i1 i2))
      (Nat.beq t (nat_lit 1)))
      (Bool.rec (motive := fun _ => Nat) KBAD (nat_lit 0) (wOK RT ph psi c rest e wl w))
      (Nat.beq t (nat_lit 0))

@[expose] noncomputable def cbK (RT X Y ADJ POS DEC : Nat) (ph : Nat → Nat) (cb Φ g0 : Nat)
    (k : Nat → Nat → Bool) : Bool :=
  strictB (Nat.land cb (nat_lit 63)) fun c =>
  strictB (treeM ADJ Φ c (Nat.shiftRight cb (nat_lit 6)) (nat_lit 0) (nat_lit 0)) fun psi =>
  strictB (Nat.land (Nat.shiftRight cb (nat_lit 6)) (nat_lit 127)) fun rt =>
  strictB (olen ph psi (nat_lit 12) rt (nat_lit 1)) fun e =>
  strictB (simpM POS DEC psi c (Nat.shiftRight cb (nat_lit 6)) (nat_lit 0)) fun sm =>
  strictB (Nat.shiftRight sm (nat_lit 80)) fun r =>
  strictB (kindOf RT X Y ph cb psi r c (Nat.land sm (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 72))
      (nat_lit 1))) e) fun kd =>
    andB (Nat.blt psi (Nat.shiftLeft (nat_lit 1) (nat_lit 72))) (andB (bit psi g0)
      (andB (Nat.blt (nat_lit 0) e) (andB (Nat.blt kd (nat_lit 4))
        (k psi (Nat.add e (Nat.add (Nat.mul (nat_lit 16) r) (Nat.add (Nat.mul (nat_lit 256) c)
          (Nat.mul (nat_lit 65536) kd))))))))

@[expose] noncomputable def dE (d : Nat) : Nat := Nat.land d (nat_lit 15)

@[expose] noncomputable def dR (d : Nat) : Nat := Nat.land (Nat.shiftRight d (nat_lit 4)) (nat_lit 15)

@[expose] noncomputable def dN (d : Nat) : Nat := Nat.land (Nat.shiftRight d (nat_lit 8)) (nat_lit 255)

@[expose] noncomputable def dK (d : Nat) : Nat := Nat.shiftRight d (nat_lit 16)

@[expose] noncomputable def lab (t r n : Nat) : Nat :=
  Nat.add t (Nat.add (Nat.mul (nat_lit 16) r) (Nat.mul (nat_lit 256) n))

@[expose] noncomputable def compLab (r N k n : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat)
        (Bool.rec (motive := fun _ => Nat) (lab (nat_lit 8) (nat_lit 0) n) (lab (nat_lit 7) (nat_lit 0) n)
          (Nat.beq r (nat_lit 6)))
        (lab (nat_lit 3) r n) (Nat.beq k (nat_lit 2)))
      (lab (nat_lit 1) r n) (Nat.beq k (nat_lit 1)))
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat)
        (Bool.rec (motive := fun _ => Nat)
          (Bool.rec (motive := fun _ => Nat) (lab (nat_lit 6) (nat_lit 0) n) (lab (nat_lit 5) (nat_lit 0) n)
            (Nat.beq r (nat_lit 7)))
          (lab (nat_lit 4) (nat_lit 0) n) (Nat.beq r (nat_lit 6)))
        (lab (nat_lit 2) r n)
        (Nat.beq N (Nat.mul (Nat.mul (nat_lit 2) r) (Nat.sub r (nat_lit 1)))))
      (lab (nat_lit 0) r n) (Nat.beq N (Nat.mul r (Nat.succ r))))
    (Nat.beq k (nat_lit 0))

@[expose] noncomputable def NOLAB : Nat := nat_lit 1099511627776

@[expose] noncomputable def extraLab (l : Nat) : Nat :=
  strictN (Nat.land l (nat_lit 15)) fun t =>
  strictN (Nat.land (Nat.shiftRight l (nat_lit 4)) (nat_lit 15)) fun r =>
  strictN (Nat.shiftRight l (nat_lit 8)) fun n =>
    Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) NOLAB
      (Bool.rec (motive := fun _ => Nat) NOLAB (lab (nat_lit 3) (nat_lit 3) n) (Nat.beq r (nat_lit 3)))
      (Nat.beq t (nat_lit 1)))
      (Bool.rec (motive := fun _ => Nat)
        (Bool.rec (motive := fun _ => Nat) NOLAB (lab (nat_lit 0) (nat_lit 1) (Nat.mul (nat_lit 2) n))
          (Nat.beq r (nat_lit 2)))
        (lab (nat_lit 1) (nat_lit 3) n) (Nat.beq r (nat_lit 3)))
      (Nat.beq t (nat_lit 3)))
      (Bool.rec (motive := fun _ => Nat) NOLAB (lab (nat_lit 0) (nat_lit 3) n) (Nat.beq r (nat_lit 3)))
      (Nat.beq t (nat_lit 2)))
      (Bool.rec (motive := fun _ => Nat)
        (Bool.rec (motive := fun _ => Nat) NOLAB (lab (nat_lit 3) (nat_lit 2) (Nat.div n (nat_lit 2)))
          (andB (Nat.beq r (nat_lit 1)) (Nat.beq (Nat.mod n (nat_lit 2)) (nat_lit 0))))
        (lab (nat_lit 2) (nat_lit 3) n) (Nat.beq r (nat_lit 3)))
      (Nat.beq t (nat_lit 0))

@[expose] noncomputable def m3 (n : Nat) : Bool :=
  Nat.beq (Nat.mod (Nat.sub (Nat.pow (nat_lit 2) n) (nat_lit 1)) (nat_lit 3)) (nat_lit 0)

@[expose] noncomputable def p3 (n : Nat) : Bool :=
  Nat.beq (Nat.mod (Nat.add (Nat.pow (nat_lit 2) n) (nat_lit 1)) (nat_lit 3)) (nat_lit 0)

@[expose] noncomputable def untw (t : Nat) : Bool :=
  orB (Nat.beq t (nat_lit 0)) (orB (Nat.beq t (nat_lit 2)) (andB (Nat.ble (nat_lit 4) t)
    (Nat.ble t (nat_lit 6))))

@[expose] noncomputable def split3 (l : Nat) : Bool :=
  strictB (Nat.land l (nat_lit 15)) fun t =>
  strictB (Nat.shiftRight l (nat_lit 8)) fun n =>
    orB (andB (untw t) (m3 n)) (orB (andB (notB (untw t)) (andB (notB (Nat.beq t (nat_lit 8))) (p3 n)))
      (orB (andB (orB (Nat.beq t (nat_lit 3)) (Nat.beq t (nat_lit 8))) (m3 n)) (Nat.beq n (nat_lit 1))))

@[expose] noncomputable def half3 (l : Nat) : Bool :=
  strictB (Nat.land l (nat_lit 15)) fun t =>
  strictB (Nat.land (Nat.shiftRight l (nat_lit 4)) (nat_lit 15)) fun r =>
  strictB (Nat.shiftRight l (nat_lit 8)) fun n =>
    orB (split3 l) (orB (andB (orB (Nat.beq t (nat_lit 2)) (orB (Nat.beq t (nat_lit 5))
      (Nat.beq t (nat_lit 6)))) (p3 n))
      (andB (orB (andB (Nat.beq t (nat_lit 1)) (Nat.beq r (nat_lit 5))) (Nat.beq t (nat_lit 7))) (m3 n)))

@[expose] noncomputable def labOf (d f : Nat) : Nat := compLab (dR d) (dN d) (dK d) (Nat.mul (dE d) f)

@[expose] noncomputable def anyLab (p : Nat → Bool) (l : Nat) : Bool :=
  strictB (extraLab l) fun l1 => orB (p l) (andB (notB (Nat.beq l1 NOLAB)) (p l1))

@[expose] noncomputable def meets (a b : Nat) : Bool :=
  strictB (extraLab b) fun b1 =>
    anyLab (fun l => orB (Nat.beq l b) (Nat.beq l b1)) a

@[expose] noncomputable def allowed (bl f dJ dx : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool)
      (andB (Nat.beq f (nat_lit 1)) (andB (Nat.beq dJ (nat_lit 531))
        (orB (Nat.beq dx (nat_lit 67107)) (orB (Nat.beq dx (nat_lit 202817))
          (Nat.beq dx (nat_lit 73297))))))
      (andB (Nat.beq f (nat_lit 2)) (andB (Nat.beq dJ (nat_lit 530))
        (orB (Nat.beq dx (nat_lit 1570)) (Nat.beq dx (nat_lit 137281)))))
      (Nat.beq bl (nat_lit 2)))
    (andB (Nat.beq f (nat_lit 1))
      (orB (andB (Nat.beq dJ (nat_lit 530))
          (orB (Nat.beq dx (nat_lit 1570)) (orB (Nat.beq dx (nat_lit 137281))
            (Nat.beq dx (nat_lit 7761)))))
        (andB (Nat.beq dJ (nat_lit 1570)) (Nat.beq dx (nat_lit 7761)))))
    (Nat.beq bl (nat_lit 0))

@[expose] noncomputable def jokX (bl f psJ dJ : Nat) (ps ds : Nat → Nat) (x : Nat) : Bool :=
  strictB (labOf dJ f) fun lJ =>
  strictB (labOf (ds x) f) fun lx =>
    orB (notB (andB (notB (Nat.beq (ps x) psJ)) (andB (anyLab split3 lx)
      (allLt (nat_lit 4) fun y => orB (Nat.beq y x)
        (strictB (labOf (ds y) f) fun ly => orB (meets ly lJ) (anyLab half3 ly))))))
      (allowed bl f dJ (ds x))

@[expose] noncomputable def jok (bl psJ dJ : Nat) (ps ds : Nat → Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (andB (allLt (nat_lit 4) (jokX bl (nat_lit 1) psJ dJ ps ds))
      (allLt (nat_lit 4) (jokX bl (nat_lit 3) psJ dJ ps ds)))
    (allLt (nat_lit 4) (jokX bl (nat_lit 2) psJ dJ ps ds))
    (Nat.beq bl (nat_lit 2))

@[expose] noncomputable def lin (u1 u2 c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun m ih => strictN ih fun a => Nat.add a (Nat.mul (Nat.pow (nat_lit 3) m)
      (Nat.mod (Nat.add (dg u1 m) (Nat.mul c (dg u2 m))) (nat_lit 3)))) (nat_lit 6)

@[expose] noncomputable def kv (RC : Nat → Nat) (x : Nat) : Nat := squash (zl LOW5 (dot5 RC x))

@[expose] noncomputable def sel4 (a b c d i : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) d c (Nat.beq i (nat_lit 2))) b (Nat.beq i (nat_lit 1)))
    a (Nat.beq i (nat_lit 0))

@[expose] noncomputable def leQ (E : Nat) : Nat := Nat.land (Nat.shiftRight E (nat_lit 1024)) (nat_lit 127)

@[expose] noncomputable def leX (E : Nat) : Nat := Nat.land (Nat.shiftRight E (nat_lit 1031)) (nat_lit 1023)

@[expose] noncomputable def leD (E : Nat) : Nat :=
  Nat.land (Nat.shiftRight E (nat_lit 1041)) (nat_lit 1048575)

@[expose] noncomputable def leP (E : Nat) : Nat := Nat.shiftRight E (nat_lit 1061)

@[expose] noncomputable def lineOK (RT X Y ADJ POS DEC NEG PW : Nat) (RC : Nat → Nat) (E : Nat) :
    Bool :=
  strictB (Nat.land E (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 1024)) (nat_lit 1))) fun cb =>
    andB (Nat.blt (leQ E) (nat_lit 75))
      (cbK RT X Y ADJ POS DEC (phq PW NEG (leQ E)) cb (kv RC (leX E))
        (Nat.land (Nat.shiftRight cb (nat_lit 6)) (nat_lit 127))
        fun p d => andB (Nat.beq p (leP E)) (Nat.beq d (leD E)))

@[expose] noncomputable def leK (LS : Nat → Nat) (q g0 jb j x : Nat) (k : Nat → Nat → Bool) : Bool :=
  strictB (LS (fld jb (nat_lit 8) (Nat.add (nat_lit 128) j))) fun E =>
    andB (Nat.beq (leQ E) q) (andB (Nat.beq (leX E) x) (andB (bit (leP E) g0) (k (leP E) (leD E))))

@[expose] noncomputable def jbOK (RT X Y ADJ POS DEC : Nat) (ph : Nat → Nat) (LS : Nat → Nat)
    (q P u1 u2 C g0 jb : Nat) : Bool :=
  cbK RT X Y ADJ POS DEC ph (fld jb (nat_lit 1024) (nat_lit 0)) P g0 fun psJ dJ =>
  andB (Nat.beq psJ C) (andB (Nat.ble (nat_lit 2) (dE dJ))
  (leK LS q g0 jb (nat_lit 0) u1 fun p0 d0 =>
  leK LS q g0 jb (nat_lit 1) u2 fun p1 d1 =>
  leK LS q g0 jb (nat_lit 2) (lin u1 u2 (nat_lit 1)) fun p2 d2 =>
  leK LS q g0 jb (nat_lit 3) (lin u1 u2 (nat_lit 2)) fun p3 d3 =>
    jok (Nat.mod q (nat_lit 3)) psJ dJ (sel4 p0 p1 p2 p3) (sel4 d0 d1 d2 d3)))

@[expose] noncomputable def compEnd (RT X Y ADJ POS DEC : Nat) (ph : Nat → Nat) (LS : Nat → Nat)
    (q P u1 u2 A C rt i : Nat) (k : Nat → Bool) : Bool :=
  strictB (olen ph C (nat_lit 12) rt (nat_lit 1)) fun e =>
    andB (Nat.blt (nat_lit 0) e)
      (Bool.rec (motive := fun _ => Bool)
        (andB (jbOK RT X Y ADJ POS DEC ph LS q P u1 u2 C rt
            (fld (Nat.shiftRight A (nat_lit 8)) (nat_lit 1056) i))
          (k (Nat.succ i)))
        (k i) (Nat.beq e (nat_lit 1)))

@[expose] noncomputable def aWalk (RT X Y ADJ POS DEC : Nat) (ph : Nat → Nat) (LS : Nat → Nat)
    (q P u1 u2 A c : Nat) : Nat → Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → Bool)
    (fun _ C rt i => compEnd RT X Y ADJ POS DEC ph LS q P u1 u2 A C rt i fun j =>
      Nat.beq j (Nat.land A (nat_lit 255)))
    (fun _ ih rest C rt i =>
      strictB (Nat.land rest (nat_lit 127)) fun g =>
      strictB (Nat.shiftLeft (nat_lit 1) g) fun bg =>
        Bool.rec (motive := fun _ => Bool)
          (ih (Nat.shiftRight rest (nat_lit 14)) (Nat.lor C bg) rt i)
          (Bool.rec (motive := fun _ => Bool)
            (compEnd RT X Y ADJ POS DEC ph LS q P u1 u2 A C rt i fun j =>
              ih (Nat.shiftRight rest (nat_lit 14)) bg g j)
            (ih (Nat.shiftRight rest (nat_lit 14)) bg g i)
            (Nat.beq C (nat_lit 0)))
          (Nat.beq g (Nat.land (Nat.shiftRight rest (nat_lit 7)) (nat_lit 127)))) c

@[expose] noncomputable def anaOK (RT X Y ADJ POS DEC NEG PW : Nat) (RC LS : Nat → Nat)
    (e A : Nat) : Bool :=
  strictB (pu1 e) fun u1 =>
  strictB (pu2 e) fun u2 =>
  strictB (pq e) fun q =>
  strictB (kmask RC u1 u2) fun P =>
    aWalk RT X Y ADJ POS DEC (phq PW NEG q) LS q P u1 u2 A
      (Nat.land (Nat.shiftRight e (nat_lit 36)) (nat_lit 127)) (Nat.shiftRight e (nat_lit 43))
      (nat_lit 0) (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def mleaf (RT X Y ADJ POS DEC NEG PW : Nat) (RC LS : Nat → Nat)
    (LF AS : Nat → Nat) (START L : Nat) : Bool :=
  strictB (fld START (nat_lit 16) (nat_lit 75)) fun tot =>
    Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
      (fun _ ih p rest =>
        strictB (Nat.land rest M547) fun e =>
        andB (orB (Nat.ble tot p) (orB (Nat.beq (Nat.land (Nat.shiftRight e (nat_lit 27)) (nat_lit 1))
            (nat_lit 0))
          (anaOK RT X Y ADJ POS DEC NEG PW RC LS e (AS (Nat.land (Nat.shiftRight e (nat_lit 28))
            (nat_lit 255))))))
          (ih (Nat.succ p) (Nat.shiftRight rest (nat_lit 547))))
      (nat_lit 16) (Nat.mul L (nat_lit 16)) (LF L)

end CFSG.TcRes.TK

end
