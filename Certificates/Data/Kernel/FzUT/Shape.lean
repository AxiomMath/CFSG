module

public import Certificates.Data.Kernel.FzUT.Norm3

public section

namespace CFSG.KC.FzUT

@[expose] noncomputable def apC (b M q : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) q (evD M q) (Nat.beq b 1)

@[expose] noncomputable def actP (T S L v q : Nat) : Nat :=
  apC (v &&& 1) T (apC ((v >>> 1) &&& 1) S (apC ((v >>> 2) &&& 1) L q))

@[expose] noncomputable def emP (T S L x y : Nat) : Nat :=
  pmulP (x &&& 63) (actP T S L (x >>> 6) (y &&& 63)) + 64 * ((x >>> 6) ^^^ (y >>> 6))

@[expose] noncomputable def pwP4 (x i : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun _ acc => pmulP acc x) i

@[expose] noncomputable def validXB (T L x : Nat) : Bool :=
  band (Nat.beq (evD T x) x) (band (Nat.beq (pwP4 x 4) 0) (band (Nat.beq (pwP4 (evD L x) 4) 0)
    (band (Nat.beq (pmulP x (evD L x)) (pmulP (evD L x) x))
      (allN 64 fun y => bimp (Nat.beq (evD T y) y)
        (anyN 16 fun k => Nat.beq (pmulP (pwP4 x (k &&& 3)) (pwP4 (evD L x) (k >>> 2))) y)))))

@[expose] noncomputable def q8B (T S L a b : Nat) : Bool :=
  sb (emP T S L a a) fun aa =>
    band (Nat.beq (emP T S L aa aa) 0) (band (Nat.beq (emP T S L b b) aa)
      (band (Nat.beq (emP T S L (emP T S L a b) a) b) (bnot (Nat.beq aa 0))))

@[expose] noncomputable def cmB (T S L u w : Nat) : Bool := Nat.beq (emP T S L u w) (emP T S L w u)

@[expose] noncomputable def gsel (G k : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (fldN G 9 511 k) 0 (Nat.beq k 7)

@[expose] noncomputable def wordP (T S L G w : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i acc => emP T S L acc (gsel G (fldN w 3 7 i))) 6

@[expose] noncomputable def shapeRel (T S L G : Nat) : Bool :=
  band (q8B T S L (fldN G 9 511 0) (fldN G 9 511 1))
  (band (q8B T S L (fldN G 9 511 2) (fldN G 9 511 3))
  (band (q8B T S L (fldN G 9 511 4) (fldN G 9 511 5))
  (band (Nat.beq (emP T S L (fldN G 9 511 4) (fldN G 9 511 4))
      (emP T S L (emP T S L (fldN G 9 511 0) (fldN G 9 511 0))
        (emP T S L (fldN G 9 511 2) (fldN G 9 511 2))))
  (band (allN 2 fun i => allN 2 fun j => cmB T S L (fldN G 9 511 i) (fldN G 9 511 (2 + j)))
  (band (allN 2 fun i => allN 2 fun j => cmB T S L (fldN G 9 511 i) (fldN G 9 511 (4 + j)))
  (band (allN 2 fun i => allN 2 fun j => cmB T S L (fldN G 9 511 (2 + i)) (fldN G 9 511 (4 + j)))
  (band (Nat.beq (emP T S L (fldN G 9 511 6) (fldN G 9 511 6)) 0)
  (band (Nat.beq (emP T S L (emP T S L (fldN G 9 511 6) (fldN G 9 511 0)) (fldN G 9 511 6))
      (fldN G 9 511 2))
  (band (Nat.beq (emP T S L (emP T S L (fldN G 9 511 6) (fldN G 9 511 1)) (fldN G 9 511 6))
      (fldN G 9 511 3))
  (band (cmB T S L (fldN G 9 511 6) (fldN G 9 511 4))
    (cmB T S L (fldN G 9 511 6) (fldN G 9 511 5))))))))))))

@[expose] noncomputable def shapeG (T S L x R : Nat) : Nat :=
  (x + 64) + 512 * (fldN R 6 63 0 + 128) + 262144 * (evD L x + 64) +
    134217728 * emP T S L (emP T S L 256 (fldN R 6 63 0 + 128)) 256 +
    68719476736 * (invP (pmulP x (evD L x)) + 64) + 35184372088832 * (fldN R 6 63 1 + 128) +
    18014398509481984 * 256

@[expose] noncomputable def shapeOK (T S L x R : Nat) : Bool :=
  sb (shapeG T S L x R) fun G => band (shapeRel T S L G)
    (allN 7 fun k => Nat.beq (wordP T S L G (fldN (R >>> 12) 18 262143 k))
      (Bool.rec (motive := fun _ => Nat) (Nat.shiftLeft 1 k) (Nat.shiftLeft 64 (k - 4))
        (Nat.blt 3 k)))

@[expose] noncomputable def shapeScan (T S L SR : Nat) : Bool :=
  allN 64 fun x => bimp (validXB T L x) (shapeOK T S L x (fldN SR 140 1393796574908163946345982392040522594123775 x))

end CFSG.KC.FzUT
