module

public import Certificates.Data.Kernel.B433Alt.Net

public section

namespace CFSG.KC.B4A

open CFSG.KC.Y333

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

@[expose] noncomputable def THM : Nat := nat_lit 0xffffff65f9843210

@[expose] noncomputable def wTh (w : Nat) : Nat :=
  sN (wLen w) (fun n => wMk n
    (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun i acc => Nat.lor acc (Nat.shiftLeft (fld THM (Nat.mul (nat_lit 4) (wAt w i)) (nat_lit 15)) (Nat.mul (nat_lit 4) i))) n))

@[expose] noncomputable def wAllLt (w m : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i acc => andB acc (Nat.blt (wAt w i) m)) (wLen w)

@[expose] noncomputable def wInT (w : Nat) : Bool :=
  andB (wOK w) (Nat.rec (motive := fun _ => Bool) true
    (fun i acc => andB acc (Nat.blt (fld THM (Nat.mul (nat_lit 4) (wAt w i)) (nat_lit 15)) (nat_lit 10))) (wLen w))

@[expose] noncomputable def wInH (w : Nat) : Bool := andB (wOK w) (wAllLt w (nat_lit 10))

@[expose] noncomputable def BASE5 : Nat := nat_lit 0x6c937b84c676e361132

@[expose] noncomputable def app5 (P c : Nat) : Nat :=
  Nat.lor (pget P (Nat.land c (nat_lit 32767)))
  (Nat.lor (Nat.shiftLeft (pget P (fld c (nat_lit 16) (nat_lit 32767))) (nat_lit 16))
  (Nat.lor (Nat.shiftLeft (pget P (fld c (nat_lit 32) (nat_lit 32767))) (nat_lit 32))
  (Nat.lor (Nat.shiftLeft (pget P (fld c (nat_lit 48) (nat_lit 32767))) (nat_lit 48))
    (Nat.shiftLeft (pget P (fld c (nat_lit 64) (nat_lit 32767))) (nat_lit 64)))))

@[expose] noncomputable def evW (LP : Nat → Nat) (w c : Nat) : Nat :=
  sN (wLen w) (fun n =>
    sN (Bool.rec (motive := fun _ => Nat) c (app5 (LP (wAt w (Nat.sub n (nat_lit 1)))) c)
        (Nat.beq (Nat.land n (nat_lit 1)) (nat_lit 1))) (fun c0 =>
    Nat.rec (motive := fun _ => Nat → Nat) (fun c => c)
      (fun i ih c => sN (app5 (LP (Nat.add (nat_lit 10) (Nat.add (Nat.mul (nat_lit 10) (wAt w (Nat.mul (nat_lit 2) i)))
          (wAt w (Nat.add (Nat.mul (nat_lit 2) i) (nat_lit 1)))))) c) (fun c' => ih c'))
      (Nat.shiftRight n (nat_lit 1)) c0))

@[expose] noncomputable def isOne (LP : Nat → Nat) (w : Nat) : Bool := Nat.beq (evW LP w BASE5) BASE5

@[expose] noncomputable def dKind (d : Nat) : Nat := Nat.land d (nat_lit 15)
@[expose] noncomputable def dN1 (d : Nat) : Nat := fld d (nat_lit 4) (nat_lit 255)
@[expose] noncomputable def dN2 (d : Nat) : Nat := fld d (nat_lit 12) (nat_lit 255)
@[expose] noncomputable def dPt (d : Nat) : Nat := fld d (nat_lit 20) (ones (nat_lit 20))
@[expose] noncomputable def dAux (d : Nat) : Nat := fld d (nat_lit 40) (nat_lit 15)

@[expose] noncomputable def isFact (k : Nat) : Bool := Nat.blt k (nat_lit 6)
@[expose] noncomputable def isStab (k : Nat) : Bool :=
  orB (Nat.beq k (nat_lit 7)) (andB (Nat.ble (nat_lit 8) k) (Nat.ble k (nat_lit 11)))
@[expose] noncomputable def isCoinc (k : Nat) : Bool := orB (Nat.beq k (nat_lit 6)) (Nat.beq k (nat_lit 12))

@[expose] noncomputable def hNat (J b : Nat) : Nat := Nat.land J (ones b)
@[expose] noncomputable def hDrop (J b : Nat) : Nat := Nat.shiftRight J b
@[expose] noncomputable def hWord (J : Nat) : Nat :=
  sN (Nat.land J (nat_lit 65535)) (fun n => wMk n (fld J (nat_lit 16) (ones (Nat.mul (nat_lit 4) n))))
@[expose] noncomputable def hAfterWord (J : Nat) : Nat :=
  Nat.shiftRight J (Nat.add (nat_lit 16) (Nat.mul (nat_lit 4) (Nat.land J (nat_lit 65535))))

section
variable (LP RD RW PW : Nat → Nat)

@[expose] noncomputable def cat3 (a b c : Nat) : Nat := wCat a (wCat b c)
@[expose] noncomputable def cat4 (a b c d : Nat) : Nat := wCat a (wCat b (wCat c d))

@[expose] noncomputable def newOK (r x tw : Nat) : Bool :=
  isOne LP (cat3 (wRev (RW r)) x (wRev (wTh tw)))

@[expose] noncomputable def ptOK (p x tw : Nat) : Bool :=
  andB (wInT tw) (isOne LP (cat3 (wRev tw) (wRev (PW p)) x))

@[expose] noncomputable def invOK (r d J : Nat) : Bool :=
  sB (hNat J (nat_lit 20)) (fun f => sB (RD f) (fun df => sB (hDrop J (nat_lit 20)) (fun J1 =>
  sB (hWord J1) (fun tw =>
    andB (Nat.blt f r) (andB (isFact (dKind df))
      (andB (Nat.beq (dN1 d) (dN2 df)) (andB (Nat.beq (dN2 d) (dN1 df))
        (andB (ptOK LP PW (dPt d) (RW f) tw)
          (newOK LP RW r (PW (dPt df)) tw)))))))))

@[expose] noncomputable def pathW (i m L : Nat) (inv : Bool) (r : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun _ ih L acc =>
      sN (Nat.land L (ones (nat_lit 20))) (fun g => sN (RD g) (fun dg =>
        Bool.rec (motive := fun _ => Nat) (nat_lit 0)
          (sN (Bool.rec (motive := fun _ => Nat) (wCat (Nat.sub acc (nat_lit 1)) (RW g))
                (wCat (wRev (RW g)) (Nat.sub acc (nat_lit 1))) inv) (fun a =>
            ih (Nat.shiftRight L (nat_lit 20)) (Nat.succ a)))
          (andB (Nat.blt (nat_lit 0) acc) (andB (Nat.blt g r)
            (andB (isStab (dKind dg)) (Nat.beq (dN2 dg) i)))))))
    m L (nat_lit 1)

@[expose] noncomputable def transOK (r d J : Nat) : Bool :=
  sB (hNat J (nat_lit 20)) (fun f => sB (RD f) (fun df =>
  sB (fld J (nat_lit 20) (ones (nat_lit 20))) (fun r0 =>
  sB (fld J (nat_lit 40) (nat_lit 255)) (fun m =>
  sB (fld J (nat_lit 48) (ones (Nat.mul (nat_lit 20) m))) (fun L =>
  sB (hWord (hDrop J (Nat.add (nat_lit 48) (Nat.mul (nat_lit 20) m)))) (fun tw =>
  sB (dN1 d) (fun i => sB (dAux d) (fun dir =>
  sB (pathW RD RW i m L (Nat.beq dir (nat_lit 1)) r) (fun s =>
    andB (Nat.blt f r) (andB (isFact (dKind df)) (andB (Nat.blt (nat_lit 0) s)
      (andB (Nat.beq (dN1 df) i) (andB (Nat.beq (dN2 d) (dN2 df)) (andB (Nat.blt dir (nat_lit 2))
        (andB (Bool.rec (motive := fun _ => Bool)
                (andB (Nat.beq (dPt d) r0) (ptOK LP PW r0 (wCat (Nat.sub s (nat_lit 1)) (PW (dPt df))) tw))
                (andB (Nat.beq (dPt df) r0) (ptOK LP PW (dPt d) (wCat (Nat.sub s (nat_lit 1)) (PW r0)) tw))
                (Nat.beq dir (nat_lit 0)))
          (newOK LP RW r (RW f) tw))))))))))))))))

@[expose] noncomputable def deadOK (r d J : Nat) : Bool :=
  sB (hNat J (nat_lit 20)) (fun f => sB (RD f) (fun df =>
  sB (fld J (nat_lit 20) (ones (nat_lit 20))) (fun c => sB (RD c) (fun dc =>
  sB (hWord (hDrop J (nat_lit 40))) (fun tw =>
    andB (Nat.blt f r) (andB (Nat.blt c r) (andB (isFact (dKind df)) (andB (isCoinc (dKind dc))
      (andB (Nat.beq (dN1 df) (dN2 dc)) (andB (Nat.beq (dN1 d) (dN1 dc)) (andB (Nat.beq (dN2 d) (dN2 df))
        (andB (ptOK LP PW (dPt d) (wCat (RW c) (PW (dPt df))) tw)
          (newOK LP RW r (RW f) tw)))))))))))))

@[expose] noncomputable def linkOK (r d J : Nat) : Bool :=
  sB (hNat J (nat_lit 20)) (fun f => sB (RD f) (fun df =>
  sB (fld J (nat_lit 20) (ones (nat_lit 20))) (fun c => sB (RD c) (fun dc =>
    andB (Nat.blt f r) (andB (Nat.blt c r) (andB (isFact (dKind df)) (andB (isCoinc (dKind dc))
      (andB (Nat.beq (dN2 df) (dN2 dc)) (andB (Nat.beq (dN1 d) (dN1 df)) (andB (Nat.beq (dPt d) (dPt df))
        (andB (Nat.beq (dN2 d) (dN1 dc))
          (isOne LP (cat3 (wRev (RW r)) (RW c) (RW f))))))))))))))

@[expose] noncomputable def twoAt (r J : Nat) (k : Nat → Nat → Nat → Nat → Bool) : Bool :=
  sB (hNat J (nat_lit 20)) (fun e => sB (RD e) (fun de =>
  sB (fld J (nat_lit 20) (ones (nat_lit 20))) (fun f => sB (RD f) (fun df =>
    andB (Nat.blt e r) (andB (Nat.blt f r) (andB (isFact (dKind de)) (andB (isFact (dKind df))
      (andB (Nat.beq (dN1 de) (dN1 df)) (andB (Nat.beq (dPt de) (dPt df)) (k e de f df))))))))))

@[expose] noncomputable def coincOK (r d J : Nat) : Bool :=
  twoAt RD r J (fun e de f df =>
    andB (notB (Nat.beq (dN2 de) (dN2 df)))
      (Bool.rec (motive := fun _ => Bool)
        (andB (Nat.beq (dN1 d) (dN2 df)) (andB (Nat.beq (dN2 d) (dN2 de))
          (isOne LP (cat3 (wRev (RW r)) (RW f) (wRev (RW e))))))
        (andB (Nat.beq (dN1 d) (dN2 de)) (andB (Nat.beq (dN2 d) (dN2 df))
          (isOne LP (cat3 (wRev (RW r)) (RW e) (wRev (RW f))))))
        (Nat.blt (dN2 de) (dN2 df))))

@[expose] noncomputable def diffOK (r d J : Nat) : Bool :=
  twoAt RD r J (fun e de f df =>
    andB (Nat.beq (dN2 de) (dN2 df)) (andB (Nat.beq (dN2 d) (dN2 de))
      (isOne LP (cat3 (wRev (RW r)) (RW e) (wRev (RW f))))))

@[expose] noncomputable def conjOK (r d J : Nat) : Bool :=
  sB (hNat J (nat_lit 20)) (fun c => sB (RD c) (fun dc =>
  sB (fld J (nat_lit 20) (ones (nat_lit 20))) (fun w => sB (RD w) (fun dw =>
    andB (Nat.blt c r) (andB (Nat.blt w r) (andB (isCoinc (dKind dc)) (andB (isStab (dKind dw))
      (andB (Nat.beq (dN2 dw) (dN2 dc)) (andB (Nat.beq (dN2 d) (dN1 dc))
        (isOne LP (cat4 (wRev (RW r)) (RW c) (RW w) (wRev (RW c)))))))))))))

@[expose] noncomputable def letOK (r d : Nat) : Bool :=
  andB (Nat.beq (dN2 d) (nat_lit 0)) (andB (Nat.blt (dAux d) (nat_lit 10)) (Nat.beq (RW r) (wOne (dAux d))))

@[expose] noncomputable def seedOK (r d J : Nat) : Bool :=
  sB (hNat J (nat_lit 20)) (fun t => sB (RD t) (fun dt =>
  sB (fld J (nat_lit 20) (ones (nat_lit 20))) (fun g => sB (RD g) (fun dg =>
  sB (fld J (nat_lit 40) (nat_lit 255)) (fun lx => sB (fld J (nat_lit 48) (nat_lit 255)) (fun ly =>
  sB (fld J (nat_lit 56) (ones (Nat.mul (nat_lit 20) lx))) (fun Lx =>
  sB (fld J (Nat.add (nat_lit 56) (Nat.mul (nat_lit 20) lx)) (ones (Nat.mul (nat_lit 20) ly))) (fun Ly =>
  sB (hWord (hDrop J (Nat.add (nat_lit 56) (Nat.mul (nat_lit 20) (Nat.add lx ly))))) (fun tw =>
  sB (dN1 dt) (fun i => sB (dPt dt) (fun r0 =>
  sB (pathW RD RW i lx Lx false r) (fun ux => sB (pathW RD RW i ly Ly true r) (fun uyi =>
    andB (Nat.blt t r) (andB (Nat.blt g r) (andB (Nat.beq (dKind dt) (nat_lit 0)) (andB (isStab (dKind dg))
      (andB (Nat.beq (dN2 dg) i) (andB (Nat.blt (nat_lit 0) ux) (andB (Nat.blt (nat_lit 0) uyi)
        (andB (Nat.beq (dN2 d) (dN2 dt))
          (andB (ptOK LP PW r0 (cat3 (Nat.sub uyi (nat_lit 1)) (RW g) (wCat (Nat.sub ux (nat_lit 1)) (PW r0))) tw)
            (isOne LP (wCat (wRev (RW r)) (wTh tw))))))))))))))))))))))))

abbrev WS := Nat × Nat

@[expose] noncomputable def sW (v : Nat) (k : Nat → WS) : WS :=
  Nat.rec (motive := fun _ => WS) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) v

@[expose] noncomputable def wsK (s : Nat) : Nat := Nat.land s (nat_lit 255)
@[expose] noncomputable def wsFail (s : Nat) : Nat := fld s (nat_lit 8) (nat_lit 1)
@[expose] noncomputable def wsJ (s : Nat) : Nat := Nat.shiftRight s (nat_lit 16)
@[expose] noncomputable def wsMk (k f J : Nat) : Nat := Nat.lor (Nat.lor k (Nat.shiftLeft f (nat_lit 8))) (Nat.shiftLeft J (nat_lit 16))

@[expose] noncomputable def walkStep (r pos : Nat) (st : WS) : WS :=
  Prod.rec (motive := fun _ => WS) (fun s x =>
    Bool.rec (motive := fun _ => WS)
      (Bool.rec (motive := fun _ => WS)
        (sW (hNat (wsJ s) (nat_lit 20)) (fun f => sW (RD f) (fun df =>
        sW (hDrop (wsJ s) (nat_lit 20)) (fun J1 => sW (hWord J1) (fun tw =>
          Bool.rec (motive := fun _ => WS) (Prod.mk (wsMk (wsK s) (nat_lit 1) (nat_lit 0)) x)
            (Prod.mk (wsMk (dN2 df) (nat_lit 0) (hAfterWord J1)) (wCat (RW f) (wTh tw)))
            (andB (Nat.blt f r) (andB (isFact (dKind df)) (andB (Nat.beq (dN1 df) (wsK s))
              (ptOK LP PW (dPt df) x tw)))))))))
        (Prod.mk s (wCat x (wOne (nat_lit 7))))
        (Nat.beq (Nat.land pos (nat_lit 1)) (nat_lit 0)))
      (Prod.mk s x)
      (Nat.beq (wsFail s) (nat_lit 1))) st

@[expose] noncomputable def walkRun (r a n : Nat) (down : Bool) : WS → WS :=
  Nat.rec (motive := fun _ => WS → WS) (fun st => st)
    (fun j ih st => Prod.rec (motive := fun _ => WS) (fun s x => sW s (fun s' => sW x (fun x' =>
        ih (walkStep LP RD RW PW r
          (Bool.rec (motive := fun _ => Nat) (Nat.add a (Nat.sub (Nat.sub n (nat_lit 1)) j))
            (Nat.sub a (Nat.sub (Nat.sub n (nat_lit 1)) j)) down)
          (Prod.mk s' x'))))) st)
    n

@[expose] noncomputable def walkOK (r d J : Nat) : Bool :=
  sB (hWord J) (fun x0 => sB (hAfterWord J) (fun J1 => sB (Nat.land J1 (nat_lit 255)) (fun i =>
  sB (dAux d) (fun f =>
    Prod.rec (motive := fun _ => Bool) (fun sf xf =>
      andB (wInH x0) (andB (Nat.ble f (nat_lit 8)) (andB (Nat.beq (wsFail sf) (nat_lit 0))
      (Bool.rec (motive := fun _ => Bool)
        (andB (Nat.beq (wsJ sf) (nat_lit 0))
          (Bool.rec (motive := fun _ => Bool)
            (andB (Nat.beq (dKind d) (nat_lit 12)) (andB (notB (Nat.beq (wsK sf) i))
              (Bool.rec (motive := fun _ => Bool)
                (andB (Nat.beq (dN1 d) (wsK sf)) (andB (Nat.beq (dN2 d) i) (isOne LP (cat3 (wRev (RW r)) xf (wRev x0)))))
                (andB (Nat.beq (dN1 d) i) (andB (Nat.beq (dN2 d) (wsK sf)) (isOne LP (cat3 (wRev (RW r)) x0 (wRev xf)))))
                (Nat.blt i (wsK sf)))))
            (andB (Nat.beq (dKind d) (nat_lit 11)) (andB (Nat.beq (dN2 d) i)
              (isOne LP (cat3 (wRev (RW r)) xf (wRev x0)))))
            (Nat.beq (wsK sf) i)))
        (Prod.rec (motive := fun _ => Bool) (fun sb xb =>
            sB (hWord (wsJ sb)) (fun tg =>
              andB (Nat.beq (dKind d) (nat_lit 5)) (andB (Nat.beq (wsFail sb) (nat_lit 0))
                (andB (Nat.beq (Nat.land (Nat.add f (nat_lit 1)) (nat_lit 1)) (nat_lit 0))
                (andB (Nat.beq (hAfterWord (wsJ sb)) (nat_lit 0))
                (andB (Nat.beq (dN1 d) (wsK sf)) (andB (Nat.beq (dN2 d) (wsK sb))
                  (andB (ptOK LP PW (dPt d) xf tg)
                    (newOK LP RW r xb tg)))))))))
          (walkRun LP RD RW PW r (nat_lit 7) (Nat.sub (nat_lit 7) f) true
            (Prod.mk (wsMk i (nat_lit 0) (wsJ sf)) x0)))
        (notB (Nat.beq f (nat_lit 8)))))))
    (walkRun LP RD RW PW r (nat_lit 0) f false (Prod.mk (wsMk i (nat_lit 0) (Nat.shiftRight J1 (nat_lit 8))) x0))))))

@[expose] noncomputable def treeOK (r _d : Nat) : Bool := Nat.beq (RW r) (nat_lit 0)

@[expose] noncomputable def recOK (r : Nat) (J : Nat) : Bool :=
  sB (RD r) (fun d => sB (dKind d) (fun k =>
    andB (wInH (RW r))
    (Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool)
          (Bool.rec (motive := fun _ => Bool)
            (Bool.rec (motive := fun _ => Bool)
              (Bool.rec (motive := fun _ => Bool)
                (Bool.rec (motive := fun _ => Bool)
                  (Bool.rec (motive := fun _ => Bool)
                    (Bool.rec (motive := fun _ => Bool)
                      (Bool.rec (motive := fun _ => Bool)
                        (andB (Nat.ble (nat_lit 11) k) (andB (Nat.ble k (nat_lit 12)) (walkOK LP RD RW PW r d J)))
                        (conjOK LP RD RW r d J) (Nat.beq k (nat_lit 10)))
                      (diffOK LP RD RW r d J) (Nat.beq k (nat_lit 9)))
                    (seedOK LP RD RW PW r d J) (Nat.beq k (nat_lit 8)))
                  (letOK RW r d) (Nat.beq k (nat_lit 7)))
                (coincOK LP RD RW r d J) (Nat.beq k (nat_lit 6)))
              (walkOK LP RD RW PW r d J) (Nat.beq k (nat_lit 5)))
            (linkOK LP RD RW r d J) (Nat.beq k (nat_lit 4)))
          (deadOK LP RD RW PW r d J) (Nat.beq k (nat_lit 3)))
        (transOK LP RD RW PW r d J) (Nat.beq k (nat_lit 2)))
      (Bool.rec (motive := fun _ => Bool) (invOK LP RD RW PW r d J) (treeOK RW r d) (Nat.beq k (nat_lit 0)))
      (Nat.ble k (nat_lit 1)))))

@[expose] noncomputable def nodeDef (S n : Nat) : Bool :=
  andB (Nat.blt n (nat_lit 64)) (Nat.blt (nat_lit 0) (Nat.land S (Nat.shiftLeft (nat_lit 1) n)))

@[expose] noncomputable def nodesOK (S d : Nat) : Bool :=
  sB (dKind d) (fun k =>
    Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool)
        (andB (nodeDef S (dN1 d)) (nodeDef S (dN2 d)))
        (nodeDef S (dN2 d)) (isStab k))
      (nodeDef S (dN1 d)) (Nat.beq k (nat_lit 0)))

@[expose] noncomputable def foldStep (RJ : Nat → Nat) (r S : Nat) : Nat :=
  sN (RD r) (fun d =>
    Bool.rec (motive := fun _ => Nat) (nat_lit 0)
      (Bool.rec (motive := fun _ => Nat) S
        (Nat.add (Nat.add S (Nat.shiftLeft (nat_lit 1) (dN2 d)))
          (Nat.shiftLeft (Nat.sub (Nat.add (dN2 d) (nat_lit 1)) (Nat.shiftRight S (nat_lit 64))) (nat_lit 64)))
        (Nat.beq (dKind d) (nat_lit 0)))
      (andB (Nat.blt (nat_lit 0) S) (andB (nodesOK S d)
        (andB (Bool.rec (motive := fun _ => Bool) true
            (andB (Nat.blt (dN2 d) (nat_lit 64)) (andB (Nat.ble (Nat.shiftRight S (nat_lit 64)) (dN2 d))
              (andB (Nat.blt (dN1 d) (dN2 d)) (notB (nodeDef S (dN2 d))))))
            (Nat.beq (dKind d) (nat_lit 0)))
          (recOK LP RD RW PW r (RJ r))))))

@[expose] noncomputable def foldRange (RJ : Nat → Nat) (a n S : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
    (fun _ ih r S => sN (foldStep LP RD RW PW RJ r S) (fun S' => ih (Nat.succ r) S'))
    n a S

@[expose] noncomputable def foldOK (RJ SS : Nat → Nat) (r : Nat) : Bool :=
  Nat.beq (foldRange LP RD RW PW RJ r (nat_lit 1) (SS r)) (SS (Nat.succ r))

end

@[expose] noncomputable def foldInit : Nat := nat_lit 1

end CFSG.KC.B4A

end
