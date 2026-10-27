module

public import Certificates.Data.Kernel.FzUT.Shape

public section

namespace CFSG.KC.FzUT

@[expose] noncomputable def bor (a b : Bool) : Bool := Bool.rec b true a

@[expose] noncomputable def invB (T S L x : Nat) : Bool :=
  band (bnot (Nat.beq x 0)) (Nat.beq (emP T S L x x) 0)

@[expose] noncomputable def inTLN (T x : Nat) : Bool :=
  band (Nat.beq (evD T (x &&& 63)) (x &&& 63)) (Nat.beq ((x >>> 6) &&& 3) 0)

@[expose] noncomputable def inWN (T x : Nat) : Bool :=
  band (Nat.beq (evD T (x &&& 63)) (x &&& 63)) (Nat.blt (x >>> 6) 2)

@[expose] noncomputable def inTZN (x : Nat) : Bool :=
  band (Nat.beq (x >>> 6) 1) (Nat.beq (x &&& 15) 0)

@[expose] noncomputable def rhoN (x : Nat) : Nat := r0P (x &&& 63) + 64 * (x >>> 6)

@[expose] noncomputable def frec (FR x : Nat) : Nat := fldN FR 40 1099511627775 x

@[expose] noncomputable def fcls (FR x : Nat) : Nat := fldN (frec FR x) 9 511 2

@[expose] noncomputable def fdep (FR x : Nat) : Nat := fldN (frec FR x) 9 511 1

@[expose] noncomputable def fpar (FR x : Nat) : Nat := fldN (frec FR x) 9 511 0

@[expose] noncomputable def fkind (FR x : Nat) : Nat := fldN (frec FR x >>> 27) 4 15 0

@[expose] noncomputable def faux (FR x : Nat) : Nat := fldN (frec FR x >>> 31) 9 511 0

@[expose] noncomputable def koutE (T S L sp l x y : Nat) : Bool :=
  band (inTLN T l) (band (Nat.beq x (emP T S L l sp)) (band (Nat.beq (emP T S L x x) 0)
    (Nat.beq y sp)))

@[expose] noncomputable def fuEdge (T S L k a x y : Nat) : Bool :=
  bor (band (Nat.beq k 1) (Nat.beq (emP T S L y a) (emP T S L a x)))
  (bor (band (Nat.beq k 2) (Nat.beq (emP T S L x a) (emP T S L a y)))
  (bor (band (Nat.beq k 3) (band (Nat.blt x 256) (Nat.beq y (rhoN x))))
  (bor (band (Nat.beq k 4) (band (Nat.blt y 256) (Nat.beq x (rhoN y))))
  (bor (band (Nat.beq k 5) (koutE T S L 128 a x y))
  (bor (band (Nat.beq k 6) (koutE T S L 128 a y x))
  (bor (band (Nat.beq k 7) (koutE T S L (emP T S L 64 128) a x y))
    (band (Nat.beq k 8) (koutE T S L (emP T S L 64 128) a y x))))))))

@[expose] noncomputable def recOK (T S L FR x : Nat) : Bool :=
  bor (band (Nat.beq (fkind FR x) 0) (band (Nat.beq (fcls FR x) x) (Nat.beq (fdep FR x) 0)))
    (band (Nat.beq (fdep FR (fpar FR x) + 1) (fdep FR x))
      (band (Nat.beq (fcls FR (fpar FR x)) (fcls FR x))
        (fuEdge T S L (fkind FR x) (faux FR x) x (fpar FR x))))

@[expose] noncomputable def forestOK (T S L FR : Nat) : Bool := allN 512 fun x => recOK T S L FR x

@[expose] noncomputable def cntN (n : Nat) (f : Nat → Bool) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i acc => Bool.rec acc (acc + 1) (f i)) n

@[expose] noncomputable def sqN (T S L x : Nat) : Nat := emP T S L x x

@[expose] noncomputable def kordN (T S L x : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat)
        (Bool.rec (motive := fun _ => Nat) 16 8
          (Nat.beq (sqN T S L (sqN T S L (sqN T S L x))) 0)) 4
        (Nat.beq (sqN T S L (sqN T S L x)) 0)) 2 (Nat.beq (sqN T S L x) 0)) 1 (Nat.beq x 0)

@[expose] noncomputable def cmN (T S L x y : Nat) : Bool := Nat.beq (emP T S L x y) (emP T S L y x)

@[expose] noncomputable def cntC (T S L w o : Nat) : Nat :=
  cntN 512 fun x => band (cmN T S L x w) (Nat.beq (kordN T S L x) o)

@[expose] noncomputable def killOK (T S L w k o : Nat) : Bool :=
  bor (band (Nat.beq k 0) (band (inTLN T w) (invB T S L w)))
  (bor (band (Nat.beq k 1) (band (inWN T w) (bnot (inTZN w))))
    (band (Nat.beq k 2) (band (Nat.ble 32 (cntN 512 fun x => cmN T S L x w))
      (Nat.blt (cntC T S L 64 o) (cntC T S L w o)))))

@[expose] noncomputable def dwit (DW i : Nat) : Nat := fldN (fldN DW 16 65535 i) 9 511 0

@[expose] noncomputable def dkind (DW i : Nat) : Nat := fldN (fldN DW 16 65535 i >>> 9) 2 3 0

@[expose] noncomputable def dord (DW i : Nat) : Nat := fldN (fldN DW 16 65535 i >>> 11) 5 31 0

@[expose] noncomputable def deadOK (T S L DW n : Nat) : Bool :=
  allN n fun i => killOK T S L (dwit DW i) (dkind DW i) (dord DW i)

@[expose] noncomputable def bxor (a b : Bool) : Bool := Bool.rec b (bnot b) a

@[expose] noncomputable def beqB (a b : Bool) : Bool := Bool.rec (bnot b) b a

@[expose] noncomputable def bitN (F i : Nat) : Bool := Nat.beq (fldN F 1 1 i) 1

@[expose] noncomputable def fE (FP FV x : Nat) : Bool := bxor (bitN FP (x &&& 63)) (bitN FV (x >>> 6))

@[expose] noncomputable def funOK (T S L FP FV : Nat) : Bool :=
  band (allN 64 fun p => allN 64 fun q => band (Nat.blt (pmulP p q) 64)
    (beqB (bitN FP (pmulP p q)) (bxor (bitN FP p) (bitN FP q))))
  (band (allN 8 fun v => allN 8 fun w => beqB (bitN FV (v ^^^ w)) (bxor (bitN FV v) (bitN FV w)))
  (band (allN 8 fun v => allN 64 fun q => band (Nat.blt (actP T S L v q) 64)
    (beqB (bitN FP (actP T S L v q)) (bitN FP q)))
  (fE FP FV 64)))

@[expose] noncomputable def coverOK (T S L FR DW n FP FV : Nat) : Bool :=
  band (funOK T S L FP FV) (allN 512 fun x => bimp (band (invB T S L x) (bnot (fE FP FV x)))
    (anyN n fun i => Nat.beq (fcls FR (dwit DW i)) (fcls FR x)))

end CFSG.KC.FzUT
