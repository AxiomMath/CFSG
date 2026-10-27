module

public import Certificates.Data.Kernel.TcRes.Moved

public section

namespace CFSG.TcRes.TK

@[expose] noncomputable def ipK8 (X Y a b : Nat) : Nat :=
  strictN (Nat.mul (fld X (nat_lit 256) a) (fld Y (nat_lit 256) b)) fun pr =>
    spk (dP (nat_lit 8) pr) (dQ (nat_lit 8) pr)

@[expose] noncomputable def LOW16 : Nat := lowW (nat_lit 16) (nat_lit 240)

@[expose] noncomputable def qOK (QS : Nat → Nat) (V i : Nat) : Bool :=
  strictB (fld V (nat_lit 128) i) fun vi =>
    allLt (nat_lit 8) fun m => Nat.beq (fld (QS m) (nat_lit 16) i) (fld vi (nat_lit 16) m)

@[expose] noncomputable def sum8 (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun m ih => strictN ih fun a => Nat.add a (f m))
    (nat_lit 8)

@[expose] noncomputable def geL (Z v : Nat) : Nat :=
  Nat.land (Nat.shiftRight (Nat.add Z (Nat.mul (Nat.sub (nat_lit 8) v) LOW16)) (nat_lit 3)) LOW16

@[expose] noncomputable def mvRow (QS : Nat → Nat) (Y x : Nat) : Nat :=
  strictN (fld Y (nat_lit 256) x) fun y =>
  strictN (sum8 fun m => Nat.mul (fld y (nat_lit 16) (Nat.sub (nat_lit 7) m)) (QS m)) fun A =>
  strictN (sum8 fun m => Nat.mul (fld y (nat_lit 16) (Nat.sub (nat_lit 15) m)) (QS m)) fun B =>
  strictN (sum8 fun m => fld y (nat_lit 16) (Nat.sub (nat_lit 7) m)) fun sp =>
  strictN (sum8 fun m => fld y (nat_lit 16) (Nat.sub (nat_lit 15) m)) fun sn =>
  strictN (Nat.sub (Nat.add A (Nat.mul (Nat.add (nat_lit 2) (Nat.mul (nat_lit 7) sn)) LOW16))
      (Nat.add B (Nat.mul (Nat.mul (nat_lit 7) sp) LOW16))) fun Z =>
  strictN (geL Z (nat_lit 1)) fun g1 =>
  strictN (geL Z (nat_lit 2)) fun g2 =>
  strictN (geL Z (nat_lit 3)) fun g3 =>
  strictN (geL Z (nat_lit 4)) fun g4 =>
    Nat.lor (Nat.sub LOW16 g1) (Nat.lor (Nat.shiftLeft (Nat.sub g1 g2) (nat_lit 3840))
      (Nat.lor (Nat.shiftLeft (Nat.sub g2 g3) (nat_lit 7680))
        (Nat.lor (Nat.shiftLeft (Nat.sub g3 g4) (nat_lit 11520)) (Nat.shiftLeft g4 (nat_lit 15360)))))

@[expose] noncomputable def mvOK (QS : Nat → Nat) (Y : Nat) (MVS : Nat → Nat) (x : Nat) : Bool :=
  Nat.beq (MVS x) (mvRow QS Y x)

@[expose] noncomputable def M240 : Nat := Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 240)) (nat_lit 1)

@[expose] noncomputable def btWalk (RTs : Nat → Nat) (ADJ BT b0 : Nat) (c : Nat) :
    Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Bool)
    (fun _ _ acc => Nat.beq acc (Nat.xor M240 (fld ADJ (nat_lit 240) (nat_lit 0))))
    (fun _ ih i prev acc =>
      strictB (fld BT (nat_lit 32) i) fun e =>
      strictB (Nat.land e (nat_lit 255)) fun g =>
      strictB (Nat.land (Nat.shiftRight e (nat_lit 8)) (nat_lit 31)) fun d =>
      strictB (Nat.land (Nat.shiftRight e (nat_lit 13)) (nat_lit 127)) fun pi =>
      strictB (fld BT (nat_lit 32) pi) fun pe =>
      strictB (Nat.shiftRight e (nat_lit 20)) fun l =>
        andB (Nat.blt prev g) (andB (Nat.blt g (nat_lit 240)) (andB (Nat.blt pi (nat_lit 126))
        (andB (notB (bit (fld ADJ (nat_lit 240) (nat_lit 0)) g))
        (andB (Bool.rec (motive := fun _ => Bool)
            (andB (Nat.beq (Nat.succ (Nat.land (Nat.shiftRight pe (nat_lit 8)) (nat_lit 31))) d)
              (andB (Nat.blt l (nat_lit 240)) (andB (notB (bit (fld ADJ (nat_lit 240) (nat_lit 0)) l))
                (Nat.beq (fld (RTs l) (nat_lit 8) (Nat.land pe (nat_lit 255))) g))))
            (Nat.beq g b0) (Nat.beq d (nat_lit 0)))
          (ih (Nat.succ i) g (Nat.lor acc (Nat.shiftLeft (nat_lit 1) g)))))))) c

@[expose] noncomputable def btOK (RTs : Nat → Nat) (ADJ BT T0 : Nat) : Bool :=
  btWalk RTs ADJ BT (fld T0 (nat_lit 8) (nat_lit 0)) (nat_lit 126) (nat_lit 0) (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def mvf (MVS : Nat → Nat) (x w : Nat) : Nat := fld (MVS x) (nat_lit 3840) w

@[expose] noncomputable def cand (X Y : Nat) (MVS : Nat → Nat) (t k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (mvf MVS k (nat_lit 2))
    (fun a ih => strictN ih fun acc => strictN (fld t (nat_lit 8) a) fun ta =>
      Nat.land acc (Nat.land
        (mvf MVS ta (Nat.sub (Nat.add (ipK8 X Y k a) (nat_lit 2)) OFS))
        (mvf MVS a (Nat.sub (Nat.add OFS (nat_lit 2)) (ipK8 X Y k ta))))) k

@[expose] noncomputable def cj8 (RTs : Nat → Nat) (t l : Nat) : Nat :=
  strictN (RTs (fld t (nat_lit 8) l)) fun ra =>
  strictN (RTs l) fun rl =>
    Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun j ih => strictN ih fun acc => Nat.lor acc (Nat.shiftLeft
        (fld rl (nat_lit 8) (fld ra (nat_lit 8) (fld t (nat_lit 8) j))) (Nat.mul (nat_lit 8) j)))
      (nat_lit 8)

@[expose] noncomputable def cjW (RTs : Nat → Nat) (wl : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ t => t)
    (fun _ ih w t => strictN (cj8 RTs t (Nat.land w (nat_lit 7))) fun t' =>
      ih (Nat.shiftRight w (nat_lit 3)) t') wl

@[expose] noncomputable def chWalk (ND t k : Nat) (c : Nat) : Nat → Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → Bool)
    (fun _ _ acc cm => Nat.beq acc cm)
    (fun _ ih j prev acc cm =>
      strictB (fld ND (nat_lit 288) j) fun r =>
      strictB (fld r (nat_lit 8) k) fun x =>
        andB (Nat.beq (Nat.land r (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 8) k)) (nat_lit 1))) t)
        (andB (Nat.beq (Nat.land (Nat.shiftRight r (nat_lit 64)) (nat_lit 15)) (Nat.succ k))
        (andB (Nat.ble prev x) (andB (bit cm (Nat.mul (nat_lit 16) x))
          (ih (Nat.succ j) (Nat.succ x)
            (Nat.lor acc (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 16) x))) cm))))) c

@[expose] noncomputable def ndOK (X Y : Nat) (RTs MVS : Nat → Nat) (ND T0 j : Nat) : Bool :=
  strictB (fld ND (nat_lit 288) j) fun r =>
  strictB (Nat.land r (nat_lit 18446744073709551615)) fun t =>
  strictB (Nat.land (Nat.shiftRight r (nat_lit 64)) (nat_lit 15)) fun k =>
    andB (Nat.ble (nat_lit 1) k) (andB (Nat.ble k (nat_lit 8))
    (andB (Nat.beq (Nat.shiftRight t (Nat.mul (nat_lit 8) k)) (nat_lit 0))
      (Bool.rec (motive := fun _ => Bool)
        (Nat.beq (cjW RTs (Nat.land (Nat.shiftRight r (nat_lit 86)) (nat_lit 63))
          (Nat.shiftRight r (nat_lit 92)) t) T0)
        (chWalk ND t k (Nat.land (Nat.shiftRight r (nat_lit 78)) (nat_lit 255))
          (Nat.land (Nat.shiftRight r (nat_lit 68)) (nat_lit 1023)) (nat_lit 0) (nat_lit 0)
          (cand X Y MVS t k))
        (Nat.blt k (nat_lit 8)))))

@[expose] noncomputable def nd0OK (ND T0 : Nat) : Bool :=
  Nat.beq (Nat.land (fld ND (nat_lit 288) (nat_lit 0)) (nat_lit 295147905179352825855))
    (Nat.add (fld T0 (nat_lit 8) (nat_lit 0)) (nat_lit 18446744073709551616))

end CFSG.TcRes.TK

end
