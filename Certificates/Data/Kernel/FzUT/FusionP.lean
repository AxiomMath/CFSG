module

public import Certificates.Data.Kernel.FzUT.Fusion

public section

namespace CFSG.KC.FzUT

@[expose] noncomputable def parN (z : Nat) : Bool := bitN 2523490710 z

@[expose] noncomputable def xtr (XT x : Nat) : Nat := fldN XT 96 79228162514264337593543950335 x

@[expose] noncomputable def xS (XT x : Nat) : Bool := bitN (xtr XT x) 0

@[expose] noncomputable def xc (XT x : Nat) : Nat := fldN (Nat.shiftRight (xtr XT x) 1) 4 15 0

@[expose] noncomputable def xk (XT x : Nat) : Nat := fldN (Nat.shiftRight (xtr XT x) 5) 5 31 0

@[expose] noncomputable def xd (XT a x : Nat) : Nat := fldN (Nat.shiftRight (xtr XT x) 10) 5 31 a

@[expose] noncomputable def xtOK (T S L XT : Nat) : Bool :=
  allN 512 fun x => band (beqB (xS XT x) (cmN T S L x 64)) (Nat.beq (xk XT x) (kordN T S L x))

@[expose] noncomputable def trec (TR x : Nat) : Nat := fldN TR 24 16777215 x

@[expose] noncomputable def tpar (TR x : Nat) : Nat := fldN (trec TR x) 9 511 0

@[expose] noncomputable def tgen (TR x : Nat) : Nat := fldN (Nat.shiftRight (trec TR x) 9) 3 7 0

@[expose] noncomputable def tdep (TR x : Nat) : Nat := fldN (Nat.shiftRight (trec TR x) 12) 12 4095 0

@[expose] noncomputable def tstep (T S L TR n : Nat) (A : Nat → Bool) (G cd : Nat → Nat)
    (x : Nat) : Bool :=
  bor (band (Nat.beq (tdep TR x) 0) (band (Nat.beq x 0) (Nat.beq (cd x) 0)))
    (band (Nat.blt (tgen TR x) n) (band (A (tpar TR x))
      (band (Nat.beq (Nat.add (tdep TR (tpar TR x)) 1) (tdep TR x))
        (band (Nat.beq x (emP T S L (tpar TR x) (G (tgen TR x))))
          (Nat.beq (cd x) (Nat.xor (cd (tpar TR x)) (Nat.shiftLeft 1 (tgen TR x))))))))

@[expose] noncomputable def treeSOK (T S L XT GS TS : Nat) : Bool :=
  band (allN 4 fun i => xS XT (fldN GS 9 511 i))
    (allN 512 fun x => bimp (xS XT x)
      (tstep T S L TS 4 (xS XT) (fun i => fldN GS 9 511 i) (xc XT) x))

@[expose] noncomputable def inK (XT a x : Nat) : Bool :=
  band (xS XT x) (bnot (parN (Nat.land a (xc XT x))))

@[expose] noncomputable def kgen (GK a j : Nat) : Nat := fldN GK 9 511 (Nat.add (Nat.mul 5 a) j)

@[expose] noncomputable def rk (RK a : Nat) : Nat := fldN RK 3 7 a

@[expose] noncomputable def treeKOK (T S L XT GK RK TK a : Nat) : Bool :=
  band (allN 5 fun j => band (inK XT a (kgen GK a j))
      (bimp (Nat.ble (rk RK a) j) (Nat.beq (kgen GK a j) 0)))
    (allN 512 fun x => bimp (inK XT a x)
      (tstep T S L (Nat.shiftRight TK (Nat.mul 12288 a)) 5 (inK XT a) (kgen GK a) (xd XT a) x))

@[expose] noncomputable def treesKOK (T S L XT GK RK TK : Nat) : Bool :=
  allN 16 fun a => bor (parN (Nat.land a (xc XT 64))) (treeKOK T S L XT GK RK TK a)

@[expose] noncomputable def thB (XT FR IN x : Nat) : Bool :=
  band (Nat.beq (xk XT x) 2) (bitN IN (fcls FR x))

@[expose] noncomputable def keyN (XT FR IN x : Nat) : Nat :=
  Nat.add (Nat.mul (xk XT x) 2) (Bool.rec (motive := fun _ => Nat) 0 1 (thB XT FR IN x))

@[expose] noncomputable def histN (f : Nat → Bool) (ky : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => Bool.rec acc (Nat.add acc (Nat.shiftLeft 1 (Nat.mul 10 (ky i)))) (f i)) 512

@[expose] noncomputable def hB (XT a b x : Nat) : Bool :=
  band (inK XT a x) (bnot (parN (Nat.land b (xd XT a x))))

@[expose] noncomputable def sbB (h : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) h

@[expose] noncomputable def profOK (T S L XT FR IN RK u : Nat) : Bool :=
  band (thB XT FR IN u) (band (Nat.blt u 512)
    (band (Nat.ble 32 (cntN 512 fun x => cmN T S L x u))
      (sbB (histN (fun x => cmN T S L x u) (keyN XT FR IN)) fun hC =>
        allN 16 fun a => bor (parN (Nat.land a (xc XT 64)))
          (allN 32 fun b => bor (Nat.ble (Nat.shiftLeft 1 (rk RK a)) b)
            (bor (parN (Nat.land b (xd XT a 64)))
              (bnot (Nat.beq (histN (hB XT a b) (keyN XT FR IN)) hC)))))))

@[expose] noncomputable def iwit (IW i : Nat) : Nat := fldN IW 9 511 i

@[expose] noncomputable def iwOK (T S L IW nI : Nat) : Bool :=
  allN nI fun i => band (inTLN T (iwit IW i)) (invB T S L (iwit IW i))

@[expose] noncomputable def inC (T S L FR IW nI U m x : Nat) : Bool :=
  bor (Nat.beq (fcls FR x) (fcls FR 64))
    (bor (anyN nI fun i => Nat.beq (fcls FR x) (fcls FR (emP T S L 64 (iwit IW i))))
      (anyN 4 fun j => band (bitN m j) (Nat.beq (fcls FR x) (fcls FR (fldN U 9 511 j)))))

@[expose] noncomputable def outC (FR DW nD U m x : Nat) : Bool :=
  bor (anyN nD fun i => Nat.beq (fcls FR (dwit DW i)) (fcls FR x))
    (anyN 4 fun j => band (bnot (bitN m j)) (Nat.beq (fcls FR x) (fcls FR (fldN U 9 511 j))))

@[expose] noncomputable def leafOK (T S L FR XT DW nD IW nI U m IN : Nat) : Bool :=
  allN 512 fun x => bimp (Nat.beq (xk XT x) 2)
    (Bool.rec (motive := fun _ => Bool) (outC FR DW nD U m x) (inC T S L FR IW nI U m x)
      (bitN IN (fcls FR x)))

@[expose] noncomputable def coverL (T S L FR IN FP FV : Nat) : Bool :=
  band (funOK T S L FP FV) (allN 512 fun x => bimp (band (invB T S L x) (bnot (fE FP FV x)))
    (bnot (bitN IN (fcls FR x))))

@[expose] noncomputable def killP (T S L FR XT DW nD IW nI U RK m IN u : Nat) : Bool :=
  band (leafOK T S L FR XT DW nD IW nI U m IN) (profOK T S L XT FR IN RK u)

@[expose] noncomputable def killC (T S L FR XT DW nD IW nI U m IN FP FV : Nat) : Bool :=
  band (leafOK T S L FR XT DW nD IW nI U m IN) (coverL T S L FR IN FP FV)

@[expose] noncomputable def lrec (LD m : Nat) : Nat := fldN LD 640 (2 ^ 640 - 1) m

@[expose] noncomputable def lIN (r : Nat) : Nat := fldN r 512 (2 ^ 512 - 1) 0

@[expose] noncomputable def leafK (T S L FR XT DW nD IW nI U RK LD m : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (killP T S L FR XT DW nD IW nI U RK m (lIN (lrec LD m))
      (fldN (Nat.shiftRight (lrec LD m) 513) 9 511 0))
    (killC T S L FR XT DW nD IW nI U m (lIN (lrec LD m))
      (fldN (Nat.shiftRight (lrec LD m) 522) 64 (2 ^ 64 - 1) 0)
      (fldN (Nat.shiftRight (lrec LD m) 586) 8 255 0))
    (bitN (lrec LD m) 512)

end CFSG.KC.FzUT
