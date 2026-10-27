module

public import Certificates.Data.Kernel.Spor.ONPvK

public section

namespace CFSG.KS.ONPw

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.ONNQ CFSG.KS.ONPv

@[expose] noncomputable def pw (f : Nat → Nat) (n x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun v => v) (fun _ ih v => strictN (f v) ih) n x

@[expose] noncomputable def sT (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (j x : Nat) : Nat :=
  iT TT UU (D j) x

@[expose] noncomputable def sU (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (j x : Nat) : Nat :=
  iU TT UU (D j) x

@[expose] noncomputable def hW (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (v x : Nat) : Nat :=
  iT (sT TT UU D) (sU TT UU D) v x

@[expose] noncomputable def hWU (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (v x : Nat) : Nat :=
  iU (sT TT UU D) (sU TT UU D) v x

@[expose] noncomputable def lT (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (k x : Nat) : Nat :=
  iT TT UU (D (Nat.add (nat_lit 3) k)) x

@[expose] noncomputable def lU (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (k x : Nat) : Nat :=
  iU TT UU (D (Nat.add (nat_lit 3) k)) x

@[expose] noncomputable def cjA (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (j x : Nat) : Nat :=
  strictN (sT TT UU D (nat_lit 12) x) fun a => strictN (sT TT UU D j a) fun c =>
    sU TT UU D (nat_lit 12) c

@[expose] noncomputable def kA (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (j x : Nat) : Nat :=
  cjA TT UU D (Nat.add (nat_lit 8) j) x

@[expose] noncomputable def fW (A K : Nat → Nat → Nat) (p : Nat) : Nat :=
  strictN (K (nat_lit 2) p) fun a => strictN (A (nat_lit 0) a) fun b =>
    strictN (A (nat_lit 2) b) fun c => strictN (K (nat_lit 1) c) fun d =>
      strictN (A (nat_lit 2) d) fun e => strictN (A (nat_lit 2) e) fun f =>
        strictN (K (nat_lit 1) f) fun g => strictN (K (nat_lit 2) g) fun h =>
          strictN (K (nat_lit 3) h) fun i => A (nat_lit 0) i

@[expose] noncomputable def bP (s : Nat) : Nat :=
  nIf(Nat.beq s (nat_lit 0), nat_lit 0, nIf(Nat.beq s (nat_lit 1), nat_lit 227759, nat_lit 100817))

@[expose] noncomputable def wAt (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (p : Nat) : Bool :=
  bAnd(Nat.beq (strictN (sU TT UU D (nat_lit 12) p) fun a => strictN (sT TT UU D (nat_lit 0) a)
      fun c => sT TT UU D (nat_lit 12) c) (pw (sT TT UU D (nat_lit 6)) (nat_lit 14) p),
    bAnd(Nat.beq (cjA TT UU D (nat_lit 6) p) (hW TT UU D (D (nat_lit 61)) p),
      bAnd(allBlk (nat_lit 8) (fun j => Nat.beq (strictN (sT TT UU D j p) (sT TT UU D (nat_lit 7)))
          (strictN (sT TT UU D (nat_lit 7) p) (sT TT UU D j))) (nat_lit 4),
        bAnd(Nat.beq (pw (sT TT UU D (nat_lit 7)) (nat_lit 7) p) p,
          Nat.beq (pw (fW (sT TT UU D) (kA TT UU D)) (nat_lit 8) p) p))))

@[expose] noncomputable def wHd (TT UU : Nat → Nat → Nat) (D : Nat → Nat) : Bool :=
  strictB (D (nat_lit 71)) fun w => strictB (Nat.land w (nat_lit 3)) fun j =>
    strictB (Nat.shiftRight w (nat_lit 2)) fun p =>
      bAnd(Nat.blt p (nat_lit 245520),
        bAnd(Bool.not (Nat.beq (strictN (kA TT UU D j p) (sT TT UU D (nat_lit 0)))
            (strictN (sT TT UU D (nat_lit 0) p) (kA TT UU D j))),
          Nat.beq (D (nat_lit 69)) (nat_lit 20160)))

@[expose] noncomputable def rt (P k : Nat) : Nat := fld(P, Nat.mul (nat_lit 7) k, nat_lit 127)

@[expose] noncomputable def rInv (P k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 120) (fun j ih => nIf(Nat.beq (rt P j) k, j, ih))
    (nat_lit 120)

@[expose] noncomputable def rG (D : Nat → Nat) (g k : Nat) : Nat := rt (D (Nat.add (nat_lit 64) g)) k

@[expose] noncomputable def rGU (D : Nat → Nat) (g k : Nat) : Nat :=
  rInv (D (Nat.add (nat_lit 64) g)) k

@[expose] noncomputable def rL (D : Nat → Nat) (g k : Nat) : Nat := rG D (Nat.add (nat_lit 3) g) k

@[expose] noncomputable def rLU (D : Nat → Nat) (g k : Nat) : Nat := rGU D (Nat.add (nat_lit 3) g) k

@[expose] noncomputable def hB (D : Nat → Nat) (v k : Nat) : Nat := iT (rG D) (rGU D) v k

@[expose] noncomputable def hBU (D : Nat → Nat) (v k : Nat) : Nat := iU (rG D) (rGU D) v k

@[expose] noncomputable def aB (D : Nat → Nat) (e k : Nat) : Nat :=
  iT (fun g => hB D (D (Nat.add (Nat.add (nat_lit 13) (Nat.mul (nat_lit 3) e)) g)))
    (fun g => hBU D (D (Nat.add (Nat.add (nat_lit 13) (Nat.mul (nat_lit 3) e)) g))) (D (nat_lit 61)) k

@[expose] noncomputable def blk (D : Nat → Nat) (k i : Nat) : Nat :=
  fld(D (nat_lit 62), Nat.add (Nat.mul (nat_lit 36) k) (Nat.mul (nat_lit 18) i), nat_lit 262143)

@[expose] noncomputable def rhoOK (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (g k : Nat) : Bool :=
  strictB (rG D g k) fun t => strictB (sT TT UU D g (blk D k (nat_lit 0))) fun m =>
    bAnd(Nat.blt t (nat_lit 120),
      bIf(Nat.beq m (blk D t (nat_lit 0)), true, Nat.beq m (blk D t (nat_lit 1))))

@[expose] noncomputable def ryOK (D : Nat → Nat) (k : Nat) : Bool :=
  Nat.beq (rt (D (nat_lit 72)) k) (hB D (D (nat_lit 61)) k)

@[expose] noncomputable def dB (D : Nat → Nat) (j : Nat) : Nat :=
  fld(D (nat_lit 63), Nat.mul (nat_lit 7) j, nat_lit 127)

@[expose] noncomputable def rhoAll (TT UU : Nat → Nat → Nat) (D : Nat → Nat) : Bool :=
  bAnd(allBlk (nat_lit 0) (fun g => allBlk (nat_lit 0) (rhoOK TT UU D g) (nat_lit 120)) (nat_lit 5),
    bAnd(allBlk (nat_lit 0) (ryOK D) (nat_lit 120),
      allBlk (nat_lit 0) (fun j => Nat.blt (dB D j) (nat_lit 120)) (nat_lit 3)))

@[expose] noncomputable def codesLt (v c : Nat) : Bool :=
  allBlk (nat_lit 0) (fun i => Nat.blt (fld(Nat.shiftRight v (nat_lit 8), Nat.mul (nat_lit 4) i,
    nat_lit 15)) c) (Nat.land v (nat_lit 255))

@[expose] noncomputable def tupM : Nat := Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 357)) (nat_lit 1)

@[expose] noncomputable def tf (T t : Nat) : Nat := fld(T, Nat.mul (nat_lit 7) t, nat_lit 127)

@[expose] noncomputable def tupOf (D : Nat → Nat) (i : Nat) : Nat :=
  Nat.land (D (Nat.add (nat_lit 80) i)) tupM

@[expose] noncomputable def tE (D : Nat → Nat) (t : Nat) : Nat :=
  nIf(Nat.blt t (nat_lit 3), dB D t,
    aB D (Nat.div (Nat.sub t (nat_lit 3)) (nat_lit 3)) (dB D (Nat.mod (Nat.sub t (nat_lit 3)) (nat_lit 3))))

@[expose] noncomputable def rootOK (D : Nat → Nat) (T : Nat) : Bool :=
  allBlk (nat_lit 0) (fun t => Nat.beq (tf T t) (tE D t)) (nat_lit 51)

@[expose] noncomputable def condT (D : Nat → Nat) (T e : Nat) : Bool :=
  allBlk (nat_lit 0) (fun j => Nat.beq (tf T (Nat.add (Nat.add (nat_lit 3) (Nat.mul (nat_lit 3) e)) j))
    (rt (D (nat_lit 72)) (tf T j))) (nat_lit 3)

@[expose] noncomputable def rB (r : Nat) : Nat := Nat.add (nat_lit 20240) (Nat.mul (nat_lit 4) r)

@[expose] noncomputable def recsAt (D : Nat → Nat) (i e cp r : Nat) : Bool :=
  allBlk (nat_lit 0) (fun k => strictB (Nat.add (Nat.add cp (Nat.mul (nat_lit 4) r)) k) fun s =>
    bAnd(Nat.blt s (D (nat_lit 70)),
      Nat.beq (Nat.land (D (rB s)) (nat_lit 2097151))
        (Nat.add i (Nat.add (Nat.shiftLeft e (nat_lit 15)) (Nat.shiftLeft k (nat_lit 19)))))) (nat_lit 4)

@[expose] noncomputable def covOK (D : Nat → Nat) (i T cp : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ ih e r => bIf(condT D T e, bAnd(recsAt D i e cp r, ih (Nat.succ e) (Nat.succ r)),
      ih (Nat.succ e) r)) (nat_lit 16) (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def sigOK (D : Nat → Nat) (i sg : Nat) : Bool :=
  bAnd(Nat.blt sg (nat_lit 20160),
    bIf(Nat.beq (Nat.succ i) (nat_lit 20160), true,
      Nat.blt (tupOf D sg)
        (tupOf D (fld(D (Nat.add (nat_lit 81) i), nat_lit 373, nat_lit 32767)))))

@[expose] noncomputable def nodeOK (D : Nat → Nat) (i : Nat) : Bool :=
  strictB (D (Nat.add (nat_lit 80) i)) fun w => strictB (Nat.land w tupM) fun T =>
    strictB (fld(w, nat_lit 357, nat_lit 32767)) fun par =>
      strictB (fld(w, nat_lit 372, nat_lit 1)) fun g =>
        bAnd(bIf(Nat.beq i (nat_lit 0), rootOK D T,
            bAnd(Nat.blt par i, strictB (tupOf D par) fun P =>
              allBlk (nat_lit 0) (fun t => Nat.beq (tf T t) (rL D g (tf P t))) (nat_lit 51))),
          bAnd(sigOK D i (fld(w, nat_lit 373, nat_lit 32767)),
            covOK D i T (Nat.shiftRight w (nat_lit 388))))

@[expose] noncomputable def nodesOK (D : Nat → Nat) (lo cnt : Nat) : Bool :=
  allN cnt fun i => nodeOK D (Nat.add lo i)

@[expose] noncomputable def lA (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (pv k x : Nat) : Nat :=
  strictN (pw (sT TT UU D (nat_lit 5)) k x) fun a => iT (lT TT UU D) (lU TT UU D) pv a

@[expose] noncomputable def lAU (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (pv k x : Nat) : Nat :=
  strictN (iU (lT TT UU D) (lU TT UU D) pv x) fun a => pw (sU TT UU D (nat_lit 5)) k a

@[expose] noncomputable def eH (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (e j x : Nat) : Nat :=
  hW TT UU D (D (Nat.add (Nat.add (nat_lit 13) (Nat.mul (nat_lit 3) e)) j)) x

@[expose] noncomputable def eHU (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (e j x : Nat) : Nat :=
  hWU TT UU D (D (Nat.add (Nat.add (nat_lit 13) (Nat.mul (nat_lit 3) e)) j)) x

@[expose] noncomputable def alA (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (pv k e j x : Nat) : Nat :=
  strictN (lAU TT UU D pv k x) fun a => strictN (eH TT UU D e j a) fun c => lA TT UU D pv k c

@[expose] noncomputable def xA (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (p : Nat) : Nat :=
  cjA TT UU D (nat_lit 7) p

@[expose] noncomputable def mode0 (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (pv k e v : Nat) : Bool :=
  bAnd(Nat.blt v (nat_lit 245520),
    Bool.not (Nat.beq (strictN (iT (eH TT UU D e) (eHU TT UU D e) (D (nat_lit 61)) v)
        (lA TT UU D pv k))
      (strictN (lA TT UU D pv k v) (cjA TT UU D (nat_lit 6)))))

@[expose] noncomputable def mode1 (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (pv k e v : Nat) : Bool :=
  bAnd(Nat.blt v (nat_lit 7),
    allBlk (nat_lit 0) (fun j => allBlk (nat_lit 0) (fun s => strictB (bP s) fun p =>
      Nat.beq (alA TT UU D pv k e j p)
        (strictN (pw (xA TT UU D) (Nat.sub (nat_lit 7) v) p) fun a =>
          strictN (sT TT UU D j a) (pw (xA TT UU D) v))) (nat_lit 3)) (nat_lit 3))

@[expose] noncomputable def mode2 (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (pv k e v u0 u2 : Nat) :
    Bool :=
  bAnd(Nat.blt v (nat_lit 245520),
    bAnd(allBlk (nat_lit 0) (fun s => strictB (bP s) fun p =>
        bAnd(Nat.beq (alA TT UU D pv k e (nat_lit 0) p) (hW TT UU D u0 p),
          Nat.beq (alA TT UU D pv k e (nat_lit 2) p) (hW TT UU D u2 p))) (nat_lit 3),
      Bool.not (Nat.beq (pw (fW (fun j => hW TT UU D (nIf(Nat.beq j (nat_lit 0), u0, u2)))
        (kA TT UU D)) (nat_lit 8) v) v)))

@[expose] noncomputable def pathOK (D : Nat → Nat) (pv n : Nat) : Bool :=
  strictB (tupOf D (nat_lit 0)) fun T0 => strictB (tupOf D n) fun T =>
    allBlk (nat_lit 0) (fun t => Nat.beq (iT (rL D) (rLU D) pv (tf T0 t)) (tf T t)) (nat_lit 51)

@[expose] noncomputable def recOK (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (r : Nat) : Bool :=
  strictB (rB r) fun b => strictB (D b) fun hd => strictB (fld(hd, nat_lit 0, nat_lit 32767)) fun n =>
    strictB (fld(hd, nat_lit 15, nat_lit 15)) fun e => strictB (fld(hd, nat_lit 19, nat_lit 3)) fun k =>
      strictB (fld(hd, nat_lit 21, nat_lit 3)) fun md => strictB (Nat.shiftRight hd (nat_lit 23)) fun v =>
        strictB (D (Nat.succ b)) fun pv =>
          bAnd(Nat.blt n (nat_lit 20160), bAnd(codesLt pv (nat_lit 4), bAnd(pathOK D pv n,
            bIf(Nat.beq md (nat_lit 0), mode0 TT UU D pv k e v,
              bIf(Nat.beq md (nat_lit 1), mode1 TT UU D pv k e v,
                bAnd(Nat.beq md (nat_lit 2),
                  strictB (D (Nat.add b (nat_lit 2))) fun u0 => strictB (D (Nat.add b (nat_lit 3))) fun u2 =>
                    bAnd(codesLt u0 (nat_lit 6), bAnd(codesLt u2 (nat_lit 6),
                      mode2 TT UU D pv k e v u0 u2))))))))

@[expose] noncomputable def recsOK (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (lo cnt : Nat) : Bool :=
  allN cnt fun r => recOK TT UU D (Nat.add lo r)

end CFSG.KS.ONPw
