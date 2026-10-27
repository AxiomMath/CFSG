module

public import Certificates.Data.Kernel.FzUT.FusionP

public section

namespace CFSG.KC.FzZ8

open CFSG.KC.FzUT

@[expose] noncomputable def invG (e : Nat → Nat → Nat) (x : Nat) : Bool :=
  band (bnot (Nat.beq x 0)) (Nat.beq (e x x) 0)

@[expose] noncomputable def koutG (e : Nat → Nat → Nat) (tl : Nat → Bool) (sp l x y : Nat) :
    Bool :=
  band (tl l) (band (Nat.beq x (e l sp)) (band (Nat.beq (e x x) 0) (Nat.beq y sp)))

@[expose] noncomputable def fuEdgeG (e : Nat → Nat → Nat) (tl : Nat → Bool) (rh : Nat → Nat)
    (k a x y : Nat) : Bool :=
  bor (band (Nat.beq k 1) (Nat.beq (e y a) (e a x)))
  (bor (band (Nat.beq k 2) (Nat.beq (e x a) (e a y)))
  (bor (band (Nat.beq k 3) (band (Nat.blt x 256) (Nat.beq y (rh x))))
  (bor (band (Nat.beq k 4) (band (Nat.blt y 256) (Nat.beq x (rh y))))
  (bor (band (Nat.beq k 5) (koutG e tl 128 a x y))
  (bor (band (Nat.beq k 6) (koutG e tl 128 a y x))
  (bor (band (Nat.beq k 7) (koutG e tl (e 64 128) a x y))
    (band (Nat.beq k 8) (koutG e tl (e 64 128) a y x))))))))

@[expose] noncomputable def recG (e : Nat → Nat → Nat) (tl : Nat → Bool) (rh : Nat → Nat)
    (FR x : Nat) : Bool :=
  bor (band (Nat.beq (fkind FR x) 0) (band (Nat.beq (fcls FR x) x) (Nat.beq (fdep FR x) 0)))
    (band (Nat.beq (fdep FR (fpar FR x) + 1) (fdep FR x))
      (band (Nat.beq (fcls FR (fpar FR x)) (fcls FR x))
        (fuEdgeG e tl rh (fkind FR x) (faux FR x) x (fpar FR x))))

@[expose] noncomputable def forestG (e : Nat → Nat → Nat) (tl : Nat → Bool) (rh : Nat → Nat)
    (FR : Nat) : Bool :=
  allN 512 fun x => recG e tl rh FR x

@[expose] noncomputable def kordG (e : Nat → Nat → Nat) (x : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat)
        (Bool.rec (motive := fun _ => Nat) 16 8
          (Nat.beq (e (e (e x x) (e x x)) (e (e x x) (e x x))) 0)) 4
        (Nat.beq (e (e x x) (e x x)) 0)) 2 (Nat.beq (e x x) 0)) 1 (Nat.beq x 0)

@[expose] noncomputable def cmG (e : Nat → Nat → Nat) (x y : Nat) : Bool :=
  Nat.beq (e x y) (e y x)

@[expose] noncomputable def cntCG (e : Nat → Nat → Nat) (w o : Nat) : Nat :=
  cntN 512 fun x => band (cmG e x w) (Nat.beq (kordG e x) o)

@[expose] noncomputable def killG (e : Nat → Nat → Nat) (tl wt tz : Nat → Bool) (w k o : Nat) :
    Bool :=
  bor (band (Nat.beq k 0) (band (tl w) (invG e w)))
  (bor (band (Nat.beq k 1) (band (wt w) (bnot (tz w))))
    (band (Nat.beq k 2) (band (Nat.ble 32 (cntN 512 fun x => cmG e x w))
      (Nat.blt (cntCG e 64 o) (cntCG e w o)))))

@[expose] noncomputable def deadG (e : Nat → Nat → Nat) (tl wt tz : Nat → Bool) (DW n : Nat) :
    Bool :=
  allN n fun i => killG e tl wt tz (dwit DW i) (dkind DW i) (dord DW i)

@[expose] noncomputable def funG (pm ac : Nat → Nat → Nat) (FP FV : Nat) : Bool :=
  band (allN 64 fun p => allN 64 fun q => band (Nat.blt (pm p q) 64)
    (beqB (bitN FP (pm p q)) (bxor (bitN FP p) (bitN FP q))))
  (band (allN 8 fun v => allN 8 fun w => beqB (bitN FV (v ^^^ w)) (bxor (bitN FV v) (bitN FV w)))
  (band (allN 8 fun v => allN 64 fun q => band (Nat.blt (ac v q) 64)
    (beqB (bitN FP (ac v q)) (bitN FP q)))
  (fE FP FV 64)))

@[expose] noncomputable def xtG (e : Nat → Nat → Nat) (XT : Nat) : Bool :=
  allN 512 fun x => band (beqB (xS XT x) (cmG e x 64)) (Nat.beq (xk XT x) (kordG e x))

@[expose] noncomputable def tstepG (e : Nat → Nat → Nat) (TR n : Nat) (A : Nat → Bool)
    (G cd : Nat → Nat) (x : Nat) : Bool :=
  bor (band (Nat.beq (tdep TR x) 0) (band (Nat.beq x 0) (Nat.beq (cd x) 0)))
    (band (Nat.blt (tgen TR x) n) (band (A (tpar TR x))
      (band (Nat.beq (Nat.add (tdep TR (tpar TR x)) 1) (tdep TR x))
        (band (Nat.beq x (e (tpar TR x) (G (tgen TR x))))
          (Nat.beq (cd x) (Nat.xor (cd (tpar TR x)) (Nat.shiftLeft 1 (tgen TR x))))))))

@[expose] noncomputable def treeSG (e : Nat → Nat → Nat) (XT GS TS : Nat) : Bool :=
  band (allN 4 fun i => xS XT (fldN GS 9 511 i))
    (allN 512 fun x => bimp (xS XT x)
      (tstepG e TS 4 (xS XT) (fun i => fldN GS 9 511 i) (xc XT) x))

@[expose] noncomputable def treeKG (e : Nat → Nat → Nat) (XT GK RK TK a : Nat) : Bool :=
  band (allN 5 fun j => band (inK XT a (kgen GK a j))
      (bimp (Nat.ble (rk RK a) j) (Nat.beq (kgen GK a j) 0)))
    (allN 512 fun x => bimp (inK XT a x)
      (tstepG e (Nat.shiftRight TK (Nat.mul 12288 a)) 5 (inK XT a) (kgen GK a) (xd XT a) x))

@[expose] noncomputable def treesKG (e : Nat → Nat → Nat) (XT GK RK TK : Nat) : Bool :=
  allN 16 fun a => bor (parN (Nat.land a (xc XT 64))) (treeKG e XT GK RK TK a)

@[expose] noncomputable def profG (e : Nat → Nat → Nat) (XT FR IN RK u : Nat) : Bool :=
  band (thB XT FR IN u) (band (Nat.blt u 512)
    (band (Nat.ble 32 (cntN 512 fun x => cmG e x u))
      (sbB (histN (fun x => cmG e x u) (keyN XT FR IN)) fun hC =>
        allN 16 fun a => bor (parN (Nat.land a (xc XT 64)))
          (allN 32 fun b => bor (Nat.ble (Nat.shiftLeft 1 (rk RK a)) b)
            (bor (parN (Nat.land b (xd XT a 64)))
              (bnot (Nat.beq (histN (hB XT a b) (keyN XT FR IN)) hC)))))))

@[expose] noncomputable def iwG (e : Nat → Nat → Nat) (tl : Nat → Bool) (IW nI : Nat) : Bool :=
  allN nI fun i => band (tl (iwit IW i)) (invG e (iwit IW i))

@[expose] noncomputable def inCG (e : Nat → Nat → Nat) (FR IW nI U m x : Nat) : Bool :=
  bor (Nat.beq (fcls FR x) (fcls FR 64))
    (bor (anyN nI fun i => Nat.beq (fcls FR x) (fcls FR (e 64 (iwit IW i))))
      (anyN 3 fun j => band (bitN m j) (Nat.beq (fcls FR x) (fcls FR (fldN U 9 511 j)))))

@[expose] noncomputable def outCG (FR DW nD U m x : Nat) : Bool :=
  bor (anyN nD fun i => Nat.beq (fcls FR (dwit DW i)) (fcls FR x))
    (anyN 3 fun j => band (bnot (bitN m j)) (Nat.beq (fcls FR x) (fcls FR (fldN U 9 511 j))))

@[expose] noncomputable def leafG (e : Nat → Nat → Nat) (FR XT DW nD IW nI U m IN : Nat) : Bool :=
  allN 512 fun x => bimp (Nat.beq (xk XT x) 2)
    (Bool.rec (motive := fun _ => Bool) (outCG FR DW nD U m x) (inCG e FR IW nI U m x)
      (bitN IN (fcls FR x)))

@[expose] noncomputable def coverLG (e pm ac : Nat → Nat → Nat) (FR IN FP FV : Nat) : Bool :=
  band (funG pm ac FP FV) (allN 512 fun x => bimp (band (invG e x) (bnot (fE FP FV x)))
    (bnot (bitN IN (fcls FR x))))

@[expose] noncomputable def leafKG (e pm ac : Nat → Nat → Nat) (FR XT DW nD IW nI U RK LD m : Nat) :
    Bool :=
  band (leafG e FR XT DW nD IW nI U m (lIN (lrec LD m)))
    (Bool.rec (motive := fun _ => Bool)
      (profG e XT FR (lIN (lrec LD m)) RK (fldN (Nat.shiftRight (lrec LD m) 513) 9 511 0))
      (coverLG e pm ac FR (lIN (lrec LD m))
        (fldN (Nat.shiftRight (lrec LD m) 522) 64 (2 ^ 64 - 1) 0)
        (fldN (Nat.shiftRight (lrec LD m) 586) 8 255 0))
      (bitN (lrec LD m) 512))

end CFSG.KC.FzZ8
