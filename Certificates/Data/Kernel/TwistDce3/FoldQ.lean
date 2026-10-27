module

public import Certificates.Data.Kernel.TwistDce3.Defs

public section

namespace CFSG.KC.TwDce3Q

open CFSG.KC.TwDce hiding evP isOne pathW wsK wsFail wsJ wsMk wsBad dKind dN1 dN2 isFact walkRun
  walkOK recOK nodesOK foldStep foldRange
open CFSG.KC.TwDce2 hiding evP isOne tStep posStep walkRun walkOK recOK foldStep foldRange
open CFSG.KC.YModel (fieldAt)

@[expose] noncomputable def ev3Q (PB : Nat) (F : Nat → Nat) (q s x y z : Nat)
    (k : Nat → Nat → Nat → Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → Bool) (fun s x y z => k s x y z)
    (fun _ ih s x y z =>
      TwDce.sB (Nat.land s (nat_lit 15)) fun a =>
      TwDce.sB (Nat.land (Nat.shiftRight s (nat_lit 4)) (nat_lit 15)) fun b =>
      TwDce.sB (Nat.land (Nat.shiftRight s (nat_lit 8)) (nat_lit 15)) fun c =>
      TwDce.sB (Nat.land (Nat.shiftRight s (nat_lit 12)) (nat_lit 15)) fun d =>
      TwDce.sB (fieldAt PB (F d) (fieldAt PB (F c) (fieldAt PB (F b) (fieldAt PB (F a) x)))) fun x' =>
      TwDce.sB (fieldAt PB (F d) (fieldAt PB (F c) (fieldAt PB (F b) (fieldAt PB (F a) y)))) fun y' =>
      TwDce.sB (fieldAt PB (F d) (fieldAt PB (F c) (fieldAt PB (F b) (fieldAt PB (F a) z)))) fun z' =>
      TwDce.sB (Nat.shiftRight s (nat_lit 16)) fun s' => ih s' x' y' z')
    q s x y z

@[expose] noncomputable def ev3T (PB : Nat) (F : Nat → Nat) (n s x y z : Nat)
    (k : Nat → Nat → Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → Bool) (fun _ x y z => k x y z)
    (fun _ ih s x y z =>
      TwDce.sB (Nat.land s (nat_lit 15)) fun a =>
      TwDce.sB (fieldAt PB (F a) x) fun x' =>
      TwDce.sB (fieldAt PB (F a) y) fun y' =>
      TwDce.sB (fieldAt PB (F a) z) fun z' =>
      TwDce.sB (Nat.shiftRight s (nat_lit 4)) fun s' => ih s' x' y' z')
    n s x y z

@[expose] noncomputable def isOneQ (PB : Nat) (F : Nat → Nat) (BS w : Nat) : Bool :=
  TwDce.sB w fun w =>
  TwDce.sB (fld BS (nat_lit 0) (nat_lit 65535)) fun b0 =>
  TwDce.sB (fld BS (nat_lit 16) (nat_lit 65535)) fun b1 =>
  TwDce.sB (fld BS (nat_lit 32) (nat_lit 65535)) fun b2 =>
  ev3Q PB F (Nat.shiftRight (wLen w) (nat_lit 2)) (wStr w) b0 b1 b2 fun s x y z =>
  ev3T PB F (Nat.land (wLen w) (nat_lit 3)) s x y z fun x y z =>
    andB (Nat.beq x b0) (andB (Nat.beq y b1) (Nat.beq z b2))

section
variable (iO : Nat → Bool) (INVM NT PSF PSB : Nat) (RD RW RA WD : Nat → Nat)

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
        (wCat (Bool.rec (motive := fun _ => Nat) (RW f) (RA f) fwd)
          (wTh (Bool.rec (motive := fun _ => Nat) PSB PSF fwd) tw)))
      (andB (Nat.blt f r) (andB (isFact (dKind df))
        (andB (Nat.beq (Bool.rec (motive := fun _ => Nat) (dN2 df) (dN1 df) fwd) k)
        (andB (Nat.blt (nat_lit 0) S) (andB (wBelow NT tw)
          (iO (wCat (wInv INVM tw) (wCat (wInv INVM w)
            (wCat (wInv INVM (Nat.sub S (nat_lit 1))) a)))))))))

@[expose] noncomputable def posStep (r w pos : Nat) (back : Bool) (st : WS) : WS :=
  Prod.rec (motive := fun _ => WS) (fun s x =>
    Bool.rec (motive := fun _ => WS)
      (TwDce.sW (wAt w pos) fun c =>
        Bool.rec (motive := fun _ => WS)
          (Bool.rec (motive := fun _ => WS)
            (tStep iO INVM NT PSF PSB RD RW RA r (wsK s) x (wsJ s)
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
        ih (posStep iO INVM NT PSF PSB RD RW RA r w
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
                  (iO (wCat (wInv INVM (RW r)) (wCat xb (wInv INVM xf))))))))
              (andB (Nat.beq (dKind d) (nat_lit 2))
                (Bool.rec (motive := fun _ => Bool)
                  (andB (Nat.beq c (nat_lit 13))
                    (andB (Nat.beq (wsK sb) (dN1 d)) (andB (Nat.beq (wsK sf) (dN2 d))
                    (andB (iO (wCat (wInv INVM (RW r)) xb))
                      (iO (wCat (wInv INVM (RA r)) xf))))))
                  (andB (Nat.beq (wsK sf) (dN1 d)) (andB (Nat.beq (wsK sb) (dN2 d))
                    (andB (iO (wCat (wInv INVM (RW r)) xf))
                      (iO (wCat (wInv INVM (RA r)) xb)))))
                  (Nat.beq c (nat_lit 12))))
              (Nat.blt c (nat_lit 14))))))))
          (walkRun iO INVM NT PSF PSB RD RW RA r w (Nat.sub (wLen w) (nat_lit 1))
            (Nat.sub (Nat.sub (wLen w) (nat_lit 1)) g) true
            (Prod.mk (wsMk i (nat_lit 0) (wsJ sf)) h0)))
      (walkRun iO INVM NT PSF PSB RD RW RA r w (nat_lit 0) g false
        (Prod.mk (wsMk i (nat_lit 0) (Nat.shiftRight J1 (nat_lit 8))) h0))

@[expose] noncomputable def recOK (r J : Nat) : Bool :=
  TwDce.sB (RD r) (fun d => TwDce.sB (dKind d) (fun k =>
    andB (wBelow (nat_lit 12) (RW r)) (andB (wBelow (nat_lit 12) (RA r))
    (Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool)
        (andB (Nat.beq k (nat_lit 4)) (andB (Nat.beq (dN1 d) (nat_lit 0)) (Nat.beq (dN2 d) (nat_lit 0))))
        (walkOK iO INVM NT PSF PSB RD RW RA WD r d J) (Nat.blt k (nat_lit 4)))
      true (Nat.blt k (nat_lit 2))))))

@[expose] noncomputable def foldStep (RJ : Nat → Nat) (r S : Nat) : Nat :=
  TwDce.sN (RD r) (fun d =>
    Bool.rec (motive := fun _ => Nat) (nat_lit 0)
      (Bool.rec (motive := fun _ => Nat) S (Nat.succ S) (isTree (dKind d)))
      (andB (Nat.blt (nat_lit 0) S) (andB (nodesOK S d)
        (recOK iO INVM NT PSF PSB RD RW RA WD r (RJ r)))))

@[expose] noncomputable def foldRange (RJ : Nat → Nat) (a n S : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
    (fun _ ih r S => TwDce.sN (foldStep iO INVM NT PSF PSB RD RW RA WD RJ r S)
      (fun S' => ih (Nat.succ r) S'))
    n a S

@[expose] noncomputable def foldIs (RJ : Nat → Nat) (a n S S' : Nat) : Bool :=
  Nat.beq (foldRange iO INVM NT PSF PSB RD RW RA WD RJ a n S) S'

end

end CFSG.KC.TwDce3Q

end
