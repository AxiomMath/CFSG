module

public import Certificates.Data.Kernel.YModel.Text

public section

namespace CFSG.KC.TwDce

open CFSG.KC.YModel

@[expose] noncomputable def sN (v : Nat) (k : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) v

@[expose] noncomputable def sB (v : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) v

@[expose] noncomputable def andB (a b : Bool) : Bool := Bool.rec false b a
@[expose] noncomputable def orB (a b : Bool) : Bool := Bool.rec b true a
@[expose] noncomputable def notB (a : Bool) : Bool := Bool.rec true false a

@[expose] noncomputable def fld (x o m : Nat) : Nat := Nat.land (Nat.shiftRight x o) m

@[expose] noncomputable def ones (n : Nat) : Nat := Nat.sub (Nat.shiftLeft (nat_lit 1) n) (nat_lit 1)

@[expose] noncomputable def wLen (w : Nat) : Nat := Nat.land w (nat_lit 4294967295)
@[expose] noncomputable def wStr (w : Nat) : Nat := Nat.shiftRight w (nat_lit 32)
@[expose] noncomputable def wMk (n s : Nat) : Nat := Nat.lor n (Nat.shiftLeft s (nat_lit 32))
@[expose] noncomputable def wOne (c : Nat) : Nat := wMk (nat_lit 1) c

@[expose] noncomputable def wAt (w i : Nat) : Nat := fld (wStr w) (Nat.mul (nat_lit 4) i) (nat_lit 15)

@[expose] noncomputable def wCat (a b : Nat) : Nat :=
  wMk (Nat.add (wLen a) (wLen b)) (Nat.lor (wStr a) (Nat.shiftLeft (wStr b) (Nat.mul (nat_lit 4) (wLen a))))

@[expose] noncomputable def wOK (w : Nat) : Bool :=
  Nat.blt (wStr w) (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 4) (wLen w)))

@[expose] noncomputable def wRev (w : Nat) : Nat :=
  sN (wLen w) (fun n => wMk n
    (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun i acc => Nat.lor acc (Nat.shiftLeft (wAt w i) (Nat.mul (nat_lit 4) (Nat.sub (Nat.sub n (nat_lit 1)) i)))) n))

@[expose] noncomputable def thL (THM c : Nat) : Nat := fld THM (Nat.mul (nat_lit 4) c) (nat_lit 15)

@[expose] noncomputable def wTh (THM w : Nat) : Nat :=
  sN (wLen w) (fun n => wMk n
    (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun i acc => Nat.lor acc (Nat.shiftLeft (thL THM (wAt w i)) (Nat.mul (nat_lit 4) i))) n))

@[expose] noncomputable def wInH (w : Nat) : Bool :=
  andB (wOK w) (Nat.rec (motive := fun _ => Bool) true
    (fun i acc => andB acc (Nat.blt (wAt w i) (nat_lit 10))) (wLen w))

@[expose] noncomputable def wInT (THM w : Nat) : Bool :=
  andB (wOK w) (Nat.rec (motive := fun _ => Bool) true
    (fun i acc => andB acc (andB (Nat.blt (wAt w i) (nat_lit 10))
      (Nat.blt (thL THM (wAt w i)) (nat_lit 10)))) (wLen w))

@[expose] noncomputable def evP (F : Nat → Nat) (w x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ x => x)
    (fun _ ih s x => sN (fieldAt (nat_lit 32) (F (Nat.land s (nat_lit 15))) x) (fun y =>
      sN (Nat.shiftRight s (nat_lit 4)) (fun s' => ih s' y)))
    (wLen w) (wStr w) x

@[expose] noncomputable def isOne (F : Nat → Nat) (BS NB w : Nat) : Bool :=
  sB w (fun w => andB (Nat.beq (Nat.land (wLen w) (nat_lit 1)) (nat_lit 0))
    (Nat.rec (motive := fun _ => Bool) true
      (fun i acc => andB acc (sB (fld BS (Nat.mul (nat_lit 16) i) (nat_lit 65535)) (fun b =>
        Nat.beq (evP F w b) b))) NB))

@[expose] noncomputable def dKind (d : Nat) : Nat := Nat.land d (nat_lit 15)
@[expose] noncomputable def dN1 (d : Nat) : Nat := fld d (nat_lit 4) (nat_lit 255)
@[expose] noncomputable def dN2 (d : Nat) : Nat := fld d (nat_lit 12) (nat_lit 255)

@[expose] noncomputable def isFact (k : Nat) : Bool := Nat.blt k (nat_lit 3)
@[expose] noncomputable def isStab (k : Nat) : Bool :=
  andB (Nat.ble (nat_lit 3) k) (Nat.blt k (nat_lit 5))

@[expose] noncomputable def hNat (J b : Nat) : Nat := Nat.land J (ones b)
@[expose] noncomputable def hDrop (J b : Nat) : Nat := Nat.shiftRight J b
@[expose] noncomputable def hWord (J : Nat) : Nat :=
  sN (Nat.land J (nat_lit 65535)) (fun n => wMk n (fld J (nat_lit 16) (ones (Nat.mul (nat_lit 4) n))))
@[expose] noncomputable def hAfterWord (J : Nat) : Nat :=
  Nat.shiftRight J (Nat.add (nat_lit 16) (Nat.mul (nat_lit 4) (Nat.land J (nat_lit 65535))))

@[expose] noncomputable def upd (F : Nat → Nat) (k v : Nat) (r : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (F r) v (Nat.beq r k)

@[expose] noncomputable def cat4 (a b c d : Nat) : Nat := wCat a (wCat b (wCat c d))

section
variable (F : Nat → Nat) (THM E BS NB : Nat) (RD RW RA : Nat → Nat)

@[expose] noncomputable def pathW (k m L r : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun _ ih L acc =>
      sN (Nat.land L (ones (nat_lit 20))) (fun g => sN (RD g) (fun dg =>
        Bool.rec (motive := fun _ => Nat) (nat_lit 0)
          (sN (Bool.rec (motive := fun _ => Nat) (wCat (Nat.sub acc (nat_lit 1)) (RW g))
                (wCat (Nat.sub acc (nat_lit 1)) (wRev (RW g)))
                (Nat.beq (fld L (nat_lit 20) (nat_lit 1)) (nat_lit 1))) (fun a =>
            ih (Nat.shiftRight L (nat_lit 21)) (Nat.succ a)))
          (andB (Nat.blt (nat_lit 0) acc) (andB (Nat.blt g r)
            (andB (isStab (dKind dg)) (Nat.beq (dN2 dg) k)))))))
    m L (nat_lit 1)

abbrev WS := Nat × Nat

@[expose] noncomputable def sW (v : Nat) (k : Nat → WS) : WS :=
  Nat.rec (motive := fun _ => WS) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) v

@[expose] noncomputable def wsK (s : Nat) : Nat := Nat.land s (nat_lit 255)
@[expose] noncomputable def wsFail (s : Nat) : Nat := fld s (nat_lit 8) (nat_lit 1)
@[expose] noncomputable def wsJ (s : Nat) : Nat := Nat.shiftRight s (nat_lit 16)
@[expose] noncomputable def wsMk (k f J : Nat) : Nat :=
  Nat.lor (Nat.lor k (Nat.shiftLeft f (nat_lit 8))) (Nat.shiftLeft J (nat_lit 16))

@[expose] noncomputable def wsBad (x : Nat) : WS := Prod.mk (wsMk (nat_lit 0) (nat_lit 1) (nat_lit 0)) x

@[expose] noncomputable def stepCore (r k a J : Nat) : WS :=
  sW (hNat J (nat_lit 20)) fun f => sW (RD f) fun df =>
  sW (fld J (nat_lit 20) (nat_lit 1)) fun dir =>
  sW (fld J (nat_lit 21) (nat_lit 255)) fun m =>
  sW (fld J (nat_lit 29) (ones (Nat.mul (nat_lit 21) m))) fun L =>
  sW (hDrop J (Nat.add (nat_lit 29) (Nat.mul (nat_lit 21) m))) fun J4 =>
  sW (hWord J4) fun tw =>
  sW (pathW RD RW k m L r) fun S =>
  sW (Bool.rec (motive := fun _ => Nat) (RA f) (RW f) (Nat.beq dir (nat_lit 0))) fun w =>
    Bool.rec (motive := fun _ => WS) (wsBad a)
      (Prod.mk
        (wsMk (Bool.rec (motive := fun _ => Nat) (dN1 df) (dN2 df) (Nat.beq dir (nat_lit 0)))
          (nat_lit 0) (hAfterWord J4))
        (wCat (Bool.rec (motive := fun _ => Nat) (RW f) (RA f) (Nat.beq dir (nat_lit 0)))
          (wTh THM tw)))
      (andB (Nat.blt f r) (andB (isFact (dKind df)) (andB (Nat.blt dir (nat_lit 2))
        (andB (Nat.beq (Bool.rec (motive := fun _ => Nat) (dN2 df) (dN1 df)
            (Nat.beq dir (nat_lit 0))) k)
        (andB (Nat.blt (nat_lit 0) S) (andB (wInT THM tw)
          (isOne F BS NB (cat4 (wRev tw) (wRev w) (wRev (Nat.sub S (nat_lit 1))) a))))))))

@[expose] noncomputable def stepRun (r : Nat) (st : WS) : WS :=
  Prod.rec (motive := fun _ => WS) (fun s a =>
    Bool.rec (motive := fun _ => WS) (stepCore F THM BS NB RD RW RA r (wsK s) a (wsJ s)) (wsBad a)
      (Nat.beq (wsFail s) (nat_lit 1))) st

@[expose] noncomputable def walkStep (r rot pos : Nat) (st : WS) : WS :=
  Prod.rec (motive := fun _ => WS) (fun s x =>
    Bool.rec (motive := fun _ => WS) (stepRun F THM BS NB RD RW RA r (Prod.mk s x))
      (Prod.mk s (wCat x (wOne E)))
      (Nat.beq (Nat.land (Nat.add pos rot) (nat_lit 1)) (nat_lit 0))) st

@[expose] noncomputable def walkRun (r rot a n : Nat) (down : Bool) : WS → WS :=
  Nat.rec (motive := fun _ => WS → WS) (fun st => st)
    (fun j ih st => Prod.rec (motive := fun _ => WS) (fun s x => sW s (fun s' => sW x (fun x' =>
        ih (walkStep F THM E BS NB RD RW RA r rot
          (Bool.rec (motive := fun _ => Nat) (Nat.add a (Nat.sub (Nat.sub n (nat_lit 1)) j))
            (Nat.sub a (Nat.sub (Nat.sub n (nat_lit 1)) j)) down)
          (Prod.mk s' x'))))) st)
    n

@[expose] noncomputable def walkOK (r d J : Nat) : Bool :=
  sB (Nat.land J (nat_lit 255)) fun i =>
  sB (hWord (hDrop J (nat_lit 8))) fun h0 =>
  sB (hAfterWord (hDrop J (nat_lit 8))) fun J1 =>
  sB (Nat.land J1 (nat_lit 1)) fun rot =>
  sB (fld J1 (nat_lit 1) (nat_lit 7)) fun g =>
    Prod.rec (motive := fun _ => Bool)
      (fun sf xf =>
        Prod.rec (motive := fun _ => Bool)
          (fun sb xb =>
            andB (wInH h0) (andB (Nat.blt E (nat_lit 10))
            (andB (Nat.beq (Nat.land (Nat.add g rot) (nat_lit 1)) (nat_lit 1))
            (andB (Nat.beq (wsFail sf) (nat_lit 0)) (andB (Nat.beq (wsFail sb) (nat_lit 0))
            (andB (Nat.beq (wsJ sb) (nat_lit 0))
            (andB (Nat.beq (wsK sf) (dN1 d)) (andB (Nat.beq (wsK sb) (dN2 d))
            (andB (isOne F BS NB (wCat (wRev (RW r)) xf))
              (isOne F BS NB (wCat (wRev (RA r)) xb)))))))))))
          (walkRun F THM E BS NB RD RW RA r rot (nat_lit 7) (Nat.sub (nat_lit 7) g) true
            (Prod.mk (wsMk i (nat_lit 0) (wsJ sf)) h0)))
      (walkRun F THM E BS NB RD RW RA r rot (nat_lit 0) g false
        (Prod.mk (wsMk i (nat_lit 0) (Nat.shiftRight J1 (nat_lit 4))) h0))

@[expose] noncomputable def factStepOK (r d J : Nat) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun s x =>
    andB (Nat.beq (wsFail s) (nat_lit 0)) (andB (Nat.beq (wsK s) (dN2 d))
      (isOne F BS NB (wCat (wRev (RA r)) x))))
    (stepRun F THM BS NB RD RW RA r (Prod.mk (wsMk (dN1 d) (nat_lit 0) J) (RW r)))

@[expose] noncomputable def diffOK (r d J : Nat) : Bool :=
  sB (Nat.land J (nat_lit 255)) (fun i => sB (hWord (hDrop J (nat_lit 8))) (fun h =>
    Prod.rec (motive := fun _ => Bool) (fun s1 x1 =>
      Prod.rec (motive := fun _ => Bool) (fun s2 x2 =>
        andB (wInH h) (andB (Nat.beq (wsFail s1) (nat_lit 0)) (andB (Nat.beq (wsFail s2) (nat_lit 0))
          (andB (Nat.beq (wsK s1) (dN2 d)) (andB (Nat.beq (wsK s2) (dN2 d))
            (isOne F BS NB (wCat (wRev (RW r)) (wCat x1 (wRev x2)))))))))
        (stepRun F THM BS NB RD RW RA r (Prod.mk (wsMk i (nat_lit 0) (wsJ s1)) h)))
      (stepRun F THM BS NB RD RW RA r (Prod.mk (wsMk i (nat_lit 0) (hAfterWord (hDrop J (nat_lit 8)))) h))))

@[expose] noncomputable def recOK (r J : Nat) : Bool :=
  sB (RD r) (fun d => sB (dKind d) (fun k =>
    andB (wInH (RW r)) (andB (wInH (RA r))
    (Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool)
          (Bool.rec (motive := fun _ => Bool)
            (andB (Nat.beq k (nat_lit 4)) (Nat.beq (dN2 d) (nat_lit 0)))
            (diffOK F THM BS NB RD RW RA r d J) (Nat.beq k (nat_lit 3)))
          (factStepOK F THM BS NB RD RW RA r d J) (Nat.beq k (nat_lit 2)))
        (walkOK F THM E BS NB RD RW RA r d J) (Nat.beq k (nat_lit 1)))
      true (Nat.beq k (nat_lit 0))))))

@[expose] noncomputable def nodesOK (S d : Nat) : Bool :=
  sB (dKind d) (fun k =>
    Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool)
        (Nat.blt (dN2 d) S)
        (andB (Nat.blt (dN1 d) S) (Nat.blt (dN2 d) S)) (isFact k))
      (andB (Nat.blt (dN1 d) S) (andB (Nat.beq (dN2 d) S) (Nat.blt S (nat_lit 255))))
      (Nat.beq k (nat_lit 0)))

@[expose] noncomputable def foldStep (RJ : Nat → Nat) (r S : Nat) : Nat :=
  sN (RD r) (fun d =>
    Bool.rec (motive := fun _ => Nat) (nat_lit 0)
      (Bool.rec (motive := fun _ => Nat) S (Nat.succ S) (Nat.beq (dKind d) (nat_lit 0)))
      (andB (Nat.blt (nat_lit 0) S) (andB (nodesOK S d) (recOK F THM E BS NB RD RW RA r (RJ r)))))

@[expose] noncomputable def foldRange (RJ : Nat → Nat) (a n S : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
    (fun _ ih r S => sN (foldStep F THM E BS NB RD RW RA RJ r S) (fun S' => ih (Nat.succ r) S'))
    n a S

end

end CFSG.KC.TwDce

end
