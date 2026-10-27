module

public import Certificates.Data.Kernel.W4Row.HS119K

public section

namespace CFSG.KC.HS119

open CFSG.KC.Ord CFSG.KC.LQT.P

@[expose] noncomputable def evS (PA G : Nat → Nat) (fuel : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ x => x)
    (fun _ ih k x => Bool.rec (motive := fun _ => Nat)
      (letN (PA k) fun r => ih (Nat.land r (nat_lit 16777215))
        (fd (nat_lit 12) (G (Nat.shiftRight r (nat_lit 24))) x))
      x (Nat.beq k (nat_lit 0))) fuel

@[expose] noncomputable def evSI (PA GI : Nat → Nat) (fuel : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ x => x)
    (fun _ ih k x => Bool.rec (motive := fun _ => Nat)
      (letN (PA k) fun r => fd (nat_lit 12) (GI (Nat.shiftRight r (nat_lit 24)))
        (ih (Nat.land r (nat_lit 16777215)) x))
      x (Nat.beq k (nat_lit 0))) fuel

@[expose] noncomputable def evL (PA G GI A AI : Nat → Nat) (c x : Nat) : Nat :=
  letN (Nat.shiftRight c (nat_lit 10)) fun t => letN (Nat.land c (nat_lit 1023)) fun v =>
    Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat)
        (Bool.rec (motive := fun _ => Nat) (fd (nat_lit 12) (AI v) x) (fd (nat_lit 12) (A v) x)
          (Nat.beq t (nat_lit 2)))
        (evSI PA GI (nat_lit 9) v x) (Nat.beq t (nat_lit 1)))
      (evS PA G (nat_lit 9) v x) (Nat.beq t (nat_lit 0))

@[expose] noncomputable def evW (Le : Nat → Nat → Nat) (W x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) x (fun i acc => Le (fd (nat_lit 12) W (Nat.succ i)) acc)
    (fd (nat_lit 12) W (nat_lit 0))

@[expose] noncomputable def evWI (Le : Nat → Nat → Nat) (W x : Nat) : Nat :=
  letN (fd (nat_lit 12) W (nat_lit 0)) fun n =>
    Nat.rec (motive := fun _ => Nat) x
      (fun i acc => Le (Nat.xor (fd (nat_lit 12) W (Nat.sub n i)) (nat_lit 1024)) acc) n

@[expose] noncomputable def bp (b5 q : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) b5 q (Nat.blt q (nat_lit 4))

@[expose] noncomputable def eq5 (b5 : Nat) (f g : Nat → Nat) : Bool :=
  allN (nat_lit 5) fun q => letB (bp b5 q) fun x => Nat.beq (f x) (g x)

@[expose] noncomputable def lIncAt (L : Nat → Nat) (j : Nat) : Bool :=
  letB (L j) fun Lj => letB (fd (nat_lit 8) Lj (nat_lit 0)) fun n =>
    allN n fun i => andB (Nat.blt (fd (nat_lit 8) Lj (Nat.succ i)) (nat_lit 192))
      (impB (Nat.blt (Nat.succ i) n)
        (Nat.blt (fd (nat_lit 8) Lj (Nat.succ i)) (fd (nat_lit 8) Lj (Nat.succ (Nat.succ i)))))

@[expose] noncomputable def depAt (PA : Nat → Nat) (k : Nat) : Bool :=
  Nat.blt (parK PA (nat_lit 0) (nat_lit 9) k) (nat_lit 2)

@[expose] noncomputable def zAt (Le : Nat → Nat → Nat) (b5 z : Nat) : Bool :=
  andB (Nat.blt z (nat_lit 1024)) (andB (Nat.blt b5 (nat_lit 3850))
    (andB (allN (nat_lit 4) fun q => Nat.beq (Le z q) q) (notB (Nat.beq (Le z b5) b5))))

@[expose] noncomputable def wordOK (p : Nat → Bool) (W : Nat) : Bool :=
  allN (fd (nat_lit 12) W (nat_lit 0)) fun i => p (fd (nat_lit 12) W (Nat.succ i))

@[expose] noncomputable def aLetOK (c : Nat) : Bool :=
  andB (Nat.ble (nat_lit 2048) c) (andB (Nat.blt c (nat_lit 4096))
    (Nat.blt (Nat.land c (nat_lit 1023)) (nat_lit 2)))

@[expose] noncomputable def cosAt (Le : Nat → Nat → Nat) (Gt KW : Nat → Nat) (gout b5 z l : Nat) :
    Bool :=
  letB (KW l) fun W => andB (wordOK aLetOK W)
    (eq5 b5 (fun x => fd (nat_lit 12) (Gt l) x) (fun x => letN (evW Le W x) fun y =>
      Bool.rec (motive := fun _ => Nat) y (Le z y) (bitB gout l)))

@[expose] noncomputable def letOK (PA : Nat → Nat) (gout : Nat) (inn : Bool) (c : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) (aLetOK c)
    (impB inn (Nat.beq (parK PA gout (nat_lit 9) (Nat.land c (nat_lit 1023))) (nat_lit 0)))
    (Nat.blt c (nat_lit 2048))

@[expose] noncomputable def witAt (Le : Nat → Nat → Nat) (PA II : Nat → Nat) (gout b5 : Nat)
    (inn : Bool) (X W V i : Nat) : Bool :=
  letB (fd (nat_lit 18) V (Nat.succ i)) fun e => letB (Nat.land e (nat_lit 255)) fun a =>
    letB (Nat.shiftRight e (nat_lit 8)) fun k =>
      andB (Nat.blt a (nat_lit 192)) (andB (bitB X a) (andB (Nat.blt k (nat_lit 1024))
        (andB (impB inn (Nat.beq (parK PA gout (nat_lit 9) k) (nat_lit 0)))
          (andB (impB (Nat.blt (Nat.succ i) (fd (nat_lit 18) V (nat_lit 0)))
              (Nat.blt a (Nat.land (fd (nat_lit 18) V (Nat.succ (Nat.succ i))) (nat_lit 255))))
            (letB (II a) fun ea => eq5 b5 (fun x => evW Le W (Le ea x))
              (fun x => Le k (evW Le W x)))))))

@[expose] noncomputable def witsOK (Le : Nat → Nat → Nat) (PA II : Nat → Nat) (gout b5 : Nat)
    (inn : Bool) (X L W V : Nat) : Bool :=
  andB (Nat.ble (fd (nat_lit 8) L (nat_lit 0)) (Nat.mul (nat_lit 4) (fd (nat_lit 18) V (nat_lit 0))))
    (allN (fd (nat_lit 18) V (nat_lit 0)) (witAt Le PA II gout b5 inn X W V))

@[expose] noncomputable def tokE (Le : Nat → Nat → Nat) (II CW : Nat → Nat) (s tok x : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (letN (CW (Nat.add (Nat.mul (nat_lit 4) s)
        (Nat.shiftRight (Nat.sub tok (nat_lit 1024)) (nat_lit 8)))) fun W =>
      letN (II (Nat.land tok (nat_lit 255))) fun ea => evW Le W (Le ea (evWI Le W x)))
    (Le tok x) (Nat.blt tok (nat_lit 1024))

@[expose] noncomputable def tokOK (PA : Nat → Nat) (gout : Nat) (inn : Bool) (m X tok : Nat) :
    Bool :=
  Bool.rec (motive := fun _ => Bool)
    (andB (Nat.blt tok (nat_lit 2048)) (andB
      (Nat.blt (Nat.shiftRight (Nat.sub tok (nat_lit 1024)) (nat_lit 8)) m)
      (andB (Nat.blt (Nat.land tok (nat_lit 255)) (nat_lit 192)) (bitB X (Nat.land tok (nat_lit 255))))))
    (impB inn (Nat.beq (parK PA gout (nat_lit 9) tok) (nat_lit 0))) (Nat.blt tok (nat_lit 1024))

@[expose] noncomputable def evY (Le : Nat → Nat → Nat) (II CW : Nat → Nat) (s Y x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) x (fun i acc => tokE Le II CW s (fd (nat_lit 12) Y (Nat.succ i)) acc)
    (fd (nat_lit 12) Y (nat_lit 0))

@[expose] noncomputable def genOK (Le : Nat → Nat → Nat) (PA II A CW : Nat → Nat) (gout b5 : Nat)
    (inn : Bool) (s m X Y t : Nat) : Bool :=
  andB (wordOK (tokOK PA gout inn m X) Y)
    (eq5 b5 (evY Le II CW s Y) (fun x => fd (nat_lit 12) (A t) x))

@[expose] noncomputable def certAt (Le : Nat → Nat → Nat) (PA II A CH CW CV CY : Nat → Nat)
    (gout b5 : Nat) (inn₀ : Bool) (s X L : Nat) : Bool :=
  letB (CH s) fun h => letB (Nat.land h (nat_lit 7)) fun m =>
    andB (Nat.ble (nat_lit 1) m) (andB (Nat.ble m (nat_lit 4)) (andB (impB inn₀ (bitB h (nat_lit 3)))
      (andB (allN m fun i => letB (CW (Nat.add (Nat.mul (nat_lit 4) s) i)) fun W =>
          andB (wordOK (letOK PA gout (bitB h (nat_lit 3))) W)
            (witsOK Le PA II gout b5 (bitB h (nat_lit 3)) X L W (CV (Nat.add (Nat.mul (nat_lit 4) s) i))))
        (allN (nat_lit 2) fun t => genOK Le PA II A CW gout b5 (bitB h (nat_lit 3)) s m X
          (CY (Nat.add (Nat.mul (nat_lit 2) s) t)) t))))

@[expose] noncomputable def hasOut (PA II : Nat → Nat) (gout L : Nat) : Bool :=
  anyN (fd (nat_lit 8) L (nat_lit 0)) fun i =>
    notB (Nat.beq (parK PA gout (nat_lit 9) (II (fd (nat_lit 8) L (Nat.succ i)))) (nat_lit 0))

@[expose] noncomputable def slotS (Le : Nat → Nat → Nat) (PA II A CH CW CV CY R L : Nat → Nat)
    (gout b5 j : Nat) : Bool :=
  impB (andB (Nat.ble (nat_lit 8) (fd (nat_lit 8) (L j) (nat_lit 0))) (hasOut PA II gout (L j)))
    (certAt Le PA II A CH CW CV CY gout b5 false j (R j) (L j))

@[expose] noncomputable def slotP (Le : Nat → Nat → Nat) (PA II A CH CW CV CY R L : Nat → Nat)
    (gout b5 nS j : Nat) : Bool :=
  impB (Nat.ble (nat_lit 8) (fd (nat_lit 8) (L j) (nat_lit 0)))
    (certAt Le PA II A CH CW CV CY gout b5 true (Nat.add nS j) (R j) (L j))

end CFSG.KC.HS119

end
