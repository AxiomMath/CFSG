module

public import Certificates.Data.Kernel.TwistDce.Defs

public section

namespace CFSG.KC.TwDce2

open CFSG.KC.TwDce

@[expose] noncomputable def ivL (INVM c : Nat) : Nat := fld INVM (Nat.mul (nat_lit 4) c) (nat_lit 15)

@[expose] noncomputable def wInv (INVM w : Nat) : Nat :=
  TwDce.sN (wLen w) (fun n => wMk n
    (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun i acc => Nat.lor acc (Nat.shiftLeft (ivL INVM (wAt w i))
        (Nat.mul (nat_lit 4) (Nat.sub (Nat.sub n (nat_lit 1)) i)))) n))

@[expose] noncomputable def wBelow (m w : Nat) : Bool :=
  andB (wOK w) (Nat.rec (motive := fun _ => Bool) true
    (fun i acc => andB acc (Nat.blt (wAt w i) m)) (wLen w))

@[expose] noncomputable def evP (F : Nat → Nat) (w x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ x => x)
    (fun _ ih s x => TwDce.sN (CFSG.KC.YModel.fieldAt (nat_lit 11) (F (Nat.land s (nat_lit 15))) x)
      (fun y => TwDce.sN (Nat.shiftRight s (nat_lit 4)) (fun s' => ih s' y)))
    (wLen w) (wStr w) x

@[expose] noncomputable def isOne (F : Nat → Nat) (BS NB w : Nat) : Bool :=
  TwDce.sB w (fun w => Nat.rec (motive := fun _ => Bool) true
      (fun i acc => andB acc (TwDce.sB (fld BS (Nat.mul (nat_lit 16) i) (nat_lit 65535)) (fun b =>
        Nat.beq (evP F w b) b))) NB)

@[expose] noncomputable def dKind (d : Nat) : Nat := Nat.land d (nat_lit 15)
@[expose] noncomputable def dN1 (d : Nat) : Nat := fld d (nat_lit 4) (nat_lit 4095)
@[expose] noncomputable def dN2 (d : Nat) : Nat := fld d (nat_lit 16) (nat_lit 4095)
@[expose] noncomputable def isFact (k : Nat) : Bool := Nat.blt k (nat_lit 3)
@[expose] noncomputable def isEq (k : Nat) : Bool := andB (Nat.ble (nat_lit 3) k) (Nat.blt k (nat_lit 5))

@[expose] noncomputable def wsK (s : Nat) : Nat := Nat.land s (nat_lit 4095)
@[expose] noncomputable def wsFail (s : Nat) : Nat := fld s (nat_lit 12) (nat_lit 1)
@[expose] noncomputable def wsJ (s : Nat) : Nat := Nat.shiftRight s (nat_lit 16)
@[expose] noncomputable def wsMk (k f J : Nat) : Nat :=
  Nat.lor (Nat.lor k (Nat.shiftLeft f (nat_lit 12))) (Nat.shiftLeft J (nat_lit 16))
@[expose] noncomputable def wsBad (x : Nat) : WS := Prod.mk (wsMk (nat_lit 0) (nat_lit 1) (nat_lit 0)) x

section
variable (F : Nat → Nat) (INVM BS NB : Nat) (RD RW RA WD : Nat → Nat)

@[expose] noncomputable def pathW (k m L r : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun _ ih L acc =>
      TwDce.sN (Nat.land L (ones (nat_lit 20))) (fun g => TwDce.sN (RD g) (fun dg =>
        Bool.rec (motive := fun _ => Nat) (nat_lit 0)
          (TwDce.sN (Bool.rec (motive := fun _ => Nat) (wCat (Nat.sub acc (nat_lit 1)) (RW g))
                (wCat (Nat.sub acc (nat_lit 1)) (wInv INVM (RW g)))
                (Nat.beq (fld L (nat_lit 20) (nat_lit 1)) (nat_lit 1))) (fun a =>
            ih (Nat.shiftRight L (nat_lit 21)) (Nat.succ a)))
          (andB (Nat.blt (nat_lit 0) acc) (andB (Nat.blt g r)
            (andB (isEq (dKind dg)) (andB (Nat.beq (dN1 dg) k) (Nat.beq (dN2 dg) k))))))))
    m L (nat_lit 1)

@[expose] noncomputable def tStep (r k a J : Nat) (fwd : Bool) : WS :=
  TwDce.sW (hNat J (nat_lit 20)) fun f => TwDce.sW (RD f) fun df =>
  TwDce.sW (fld J (nat_lit 20) (nat_lit 255)) fun m =>
  TwDce.sW (fld J (nat_lit 28) (ones (Nat.mul (nat_lit 21) m))) fun L =>
  TwDce.sW (hDrop J (Nat.add (nat_lit 28) (Nat.mul (nat_lit 21) m))) fun J4 =>
  TwDce.sW (hWord J4) fun tw =>
  TwDce.sW (pathW INVM RD RW k m L r) fun S =>
  TwDce.sW (Bool.rec (motive := fun _ => Nat) (RA f) (RW f) fwd) fun w =>
    Bool.rec (motive := fun _ => WS) (wsBad a)
      (Prod.mk
        (wsMk (Bool.rec (motive := fun _ => Nat) (dN1 df) (dN2 df) fwd) (nat_lit 0) (hAfterWord J4))
        (wCat (Bool.rec (motive := fun _ => Nat) (RW f) (RA f) fwd) tw))
      (andB (Nat.blt f r) (andB (isFact (dKind df))
        (andB (Nat.beq (Bool.rec (motive := fun _ => Nat) (dN2 df) (dN1 df) fwd) k)
        (andB (Nat.blt (nat_lit 0) S) (andB (wBelow (nat_lit 4) tw)
          (isOne F BS NB (wCat (wInv INVM tw) (wCat (wInv INVM w)
            (wCat (wInv INVM (Nat.sub S (nat_lit 1))) a)))))))))

@[expose] noncomputable def eStep (r k a J : Nat) (back : Bool) : WS :=
  TwDce.sW (hNat J (nat_lit 20)) fun e => TwDce.sW (RD e) fun de =>
  TwDce.sW (Bool.rec (motive := fun _ => Nat) (fld J (nat_lit 20) (nat_lit 1))
    (Nat.sub (nat_lit 1) (fld J (nat_lit 20) (nat_lit 1))) back) fun dir =>
    Bool.rec (motive := fun _ => WS) (wsBad a)
      (Bool.rec (motive := fun _ => WS)
        (Prod.mk (wsMk (dN1 de) (nat_lit 0) (hDrop J (nat_lit 21))) (wCat (wInv INVM (RW e)) a))
        (Prod.mk (wsMk (dN2 de) (nat_lit 0) (hDrop J (nat_lit 21))) (wCat (RW e) a))
        (Nat.beq dir (nat_lit 0)))
      (andB (Nat.blt e r) (andB (isEq (dKind de))
        (Nat.beq (Bool.rec (motive := fun _ => Nat) (dN2 de) (dN1 de) (Nat.beq dir (nat_lit 0))) k)))

@[expose] noncomputable def posStep (r w pos : Nat) (back : Bool) (st : WS) : WS :=
  Prod.rec (motive := fun _ => WS) (fun s x =>
    Bool.rec (motive := fun _ => WS)
      (TwDce.sW (wAt w pos) fun c =>
        Bool.rec (motive := fun _ => WS)
          (Bool.rec (motive := fun _ => WS)
            (tStep F INVM BS NB RD RW RA r (wsK s) x (wsJ s)
              (Bool.rec (motive := fun _ => Bool) (Nat.beq c (nat_lit 12)) (Nat.beq c (nat_lit 13)) back))
            (eStep INVM RD RW r (wsK s) x (wsJ s) back)
            (Nat.beq c (nat_lit 14)))
          (Prod.mk s (wCat x (wOne (Bool.rec (motive := fun _ => Nat) c (ivL INVM c) back))))
          (Nat.blt c (nat_lit 12)))
      (wsBad x)
      (Nat.beq (wsFail s) (nat_lit 1))) st

@[expose] noncomputable def walkRun (r w a n : Nat) (back : Bool) : WS → WS :=
  Nat.rec (motive := fun _ => WS → WS) (fun st => st)
    (fun j ih st => Prod.rec (motive := fun _ => WS) (fun s x => TwDce.sW s (fun s' => TwDce.sW x (fun x' =>
        ih (posStep F INVM BS NB RD RW RA r w
          (Bool.rec (motive := fun _ => Nat) (Nat.add a (Nat.sub (Nat.sub n (nat_lit 1)) j))
            (Nat.sub a (Nat.sub (Nat.sub n (nat_lit 1)) j)) back) back
          (Prod.mk s' x'))))) st)
    n

@[expose] noncomputable def walkOK (r d J : Nat) : Bool :=
  TwDce.sB (WD (Nat.land J (nat_lit 4095))) fun w =>
  TwDce.sB (fld J (nat_lit 12) (nat_lit 4095)) fun i =>
  TwDce.sB (hWord (hDrop J (nat_lit 24))) fun h0 =>
  TwDce.sB (hAfterWord (hDrop J (nat_lit 24))) fun J1 =>
  TwDce.sB (Nat.land J1 (nat_lit 255)) fun g =>
  TwDce.sB (wAt w g) fun c =>
    Prod.rec (motive := fun _ => Bool)
      (fun sf xf =>
        Prod.rec (motive := fun _ => Bool)
          (fun sb xb =>
            andB (wBelow (nat_lit 12) h0) (andB (Nat.blt g (wLen w))
            (andB (Nat.beq (wsFail sf) (nat_lit 0)) (andB (Nat.beq (wsFail sb) (nat_lit 0))
            (andB (Nat.beq (wsJ sb) (nat_lit 0))
            (Bool.rec (motive := fun _ => Bool)
              (andB (Nat.beq c (nat_lit 14)) (andB (Nat.beq (dKind d) (nat_lit 3))
                (andB (Nat.beq (wsK sf) (dN1 d)) (andB (Nat.beq (wsK sb) (dN2 d))
                  (isOne F BS NB (wCat (wInv INVM (RW r)) (wCat xb (wInv INVM xf))))))))
              (andB (Nat.beq (dKind d) (nat_lit 2))
                (Bool.rec (motive := fun _ => Bool)
                  (andB (Nat.beq c (nat_lit 13))
                    (andB (Nat.beq (wsK sb) (dN1 d)) (andB (Nat.beq (wsK sf) (dN2 d))
                    (andB (isOne F BS NB (wCat (wInv INVM (RW r)) xb))
                      (isOne F BS NB (wCat (wInv INVM (RA r)) xf))))))
                  (andB (Nat.beq (wsK sf) (dN1 d)) (andB (Nat.beq (wsK sb) (dN2 d))
                    (andB (isOne F BS NB (wCat (wInv INVM (RW r)) xf))
                      (isOne F BS NB (wCat (wInv INVM (RA r)) xb)))))
                  (Nat.beq c (nat_lit 12))))
              (Nat.blt c (nat_lit 14))))))))
          (walkRun F INVM BS NB RD RW RA r w (Nat.sub (wLen w) (nat_lit 1))
            (Nat.sub (Nat.sub (wLen w) (nat_lit 1)) g) true
            (Prod.mk (wsMk i (nat_lit 0) (wsJ sf)) h0)))
      (walkRun F INVM BS NB RD RW RA r w (nat_lit 0) g false
        (Prod.mk (wsMk i (nat_lit 0) (Nat.shiftRight J1 (nat_lit 8))) h0))

@[expose] noncomputable def recOK (r J : Nat) : Bool :=
  TwDce.sB (RD r) (fun d => TwDce.sB (dKind d) (fun k =>
    andB (wBelow (nat_lit 12) (RW r)) (andB (wBelow (nat_lit 12) (RA r))
    (Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool)
        (andB (Nat.beq k (nat_lit 4)) (andB (Nat.beq (dN1 d) (nat_lit 0)) (Nat.beq (dN2 d) (nat_lit 0))))
        (walkOK F INVM BS NB RD RW RA WD r d J) (Nat.blt k (nat_lit 4)))
      true (Nat.blt k (nat_lit 2))))))

@[expose] noncomputable def nodesOK (S d : Nat) : Bool :=
  TwDce.sB (dKind d) (fun k =>
    andB (Nat.blt S (nat_lit 4095))
    (Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool)
        (andB (Nat.blt (dN1 d) S) (Nat.blt (dN2 d) S))
        (andB (Nat.beq (dN1 d) S) (Nat.blt (dN2 d) S)) (Nat.beq k (nat_lit 1)))
      (andB (Nat.blt (dN1 d) S) (Nat.beq (dN2 d) S))
      (Nat.beq k (nat_lit 0))))

@[expose] noncomputable def isTree (k : Nat) : Bool := Nat.blt k (nat_lit 2)

@[expose] noncomputable def foldStep (RJ : Nat → Nat) (r S : Nat) : Nat :=
  TwDce.sN (RD r) (fun d =>
    Bool.rec (motive := fun _ => Nat) (nat_lit 0)
      (Bool.rec (motive := fun _ => Nat) S (Nat.succ S) (isTree (dKind d)))
      (andB (Nat.blt (nat_lit 0) S) (andB (nodesOK S d) (recOK F INVM BS NB RD RW RA WD r (RJ r)))))

@[expose] noncomputable def foldRange (RJ : Nat → Nat) (a n S : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
    (fun _ ih r S => TwDce.sN (foldStep F INVM BS NB RD RW RA WD RJ r S) (fun S' => ih (Nat.succ r) S'))
    n a S

end

end CFSG.KC.TwDce2

end
