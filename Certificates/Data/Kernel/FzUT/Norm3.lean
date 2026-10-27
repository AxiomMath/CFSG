module

public import Certificates.Data.Kernel.FzUT.Codes

public section

namespace CFSG.KC.FzUT

@[expose] noncomputable def band (a b : Bool) : Bool := Bool.rec false b a

@[expose] noncomputable def bimp (c a : Bool) : Bool := Bool.rec true a c

@[expose] noncomputable def bnot (a : Bool) : Bool := Bool.rec true false a

@[expose] noncomputable def allN (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => band (f i) ih) n

@[expose] noncomputable def anyN (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun i ih => Bool.rec ih true (f i)) n

@[expose] noncomputable def sb (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def fldN (P w m i : Nat) : Nat := Nat.land (Nat.shiftRight P (Nat.mul w i)) m

@[expose] noncomputable def c4 (d i : Nat) : Nat := fldN d 6 63 i

@[expose] noncomputable def evD (d x : Nat) : Nat := evN (c4 d 0) (c4 d 1) (c4 d 2) (c4 d 3) x

@[expose] noncomputable def pk4 (a b c d : Nat) : Nat := a + 64 * b + 4096 * c + 262144 * d

@[expose] noncomputable def r0P (x : Nat) : Nat := evN 3 1 12 4 x

@[expose] noncomputable def invP (x : Nat) : Nat := x ^^^ 16 * f4mulP (x &&& 3) ((x >>> 2) &&& 3)

@[expose] noncomputable def tauP (x : Nat) : Nat :=
  ((x >>> 2) &&& 3) + 4 * (x &&& 3) + 16 * ((x >>> 4) ^^^ f4mulP (x &&& 3) ((x >>> 2) &&& 3))

@[expose] noncomputable def scP (lam mu q q' x : Nat) : Nat :=
  f4mulP lam (x &&& 3) + 4 * f4mulP mu ((x >>> 2) &&& 3) +
    16 * (f4mulP (f4mulP lam mu) (x >>> 4) ^^^ f4mulP q (f4mulP (x &&& 3) (x &&& 3)) ^^^
      f4mulP q' (f4mulP ((x >>> 2) &&& 3) ((x >>> 2) &&& 3)))

@[expose] noncomputable def betaP (p x : Nat) : Nat :=
  scP (p &&& 3) ((p >>> 2) &&& 3) ((p >>> 4) &&& 3) ((p >>> 6) &&& 3)
    (Bool.rec (motive := fun _ => Nat) x (tauP x) (Nat.beq ((p >>> 8) &&& 1) 1))

@[expose] noncomputable def pOK (p : Nat) : Bool :=
  band (bnot (Nat.beq (p &&& 3) 0)) (bnot (Nat.beq ((p >>> 2) &&& 3) 0))

@[expose] noncomputable def conjOK (p Y T T' : Nat) : Bool :=
  allN 4 fun k => band (Nat.beq (betaP p (c4 Y k)) (Nat.shiftLeft 1 k))
    (Nat.beq (betaP p (evD T (c4 Y k))) (c4 T' k))

@[expose] noncomputable def rhoOK (p : Nat) : Bool :=
  allN 4 fun k => Nat.beq (betaP p (r0P (Nat.shiftLeft 1 k))) (r0P (betaP p (Nat.shiftLeft 1 k)))

@[expose] noncomputable def elemabOK (T : Nat) : Bool :=
  allN 64 fun x => bimp (Nat.beq (evD T x) x) (Nat.beq (pmulP x x) 0)

@[expose] noncomputable def tRecOK (TG T R : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool)
      (band (Nat.beq (R &&& 3) 2) (band (pOK ((R >>> 2) &&& 511)) (band (rhoOK ((R >>> 2) &&& 511))
        (conjOK ((R >>> 2) &&& 511) (R >>> 13) T (fldN TG 24 16777215 ((R >>> 11) &&& 3))))))
      (elemabOK T) (Nat.beq (R &&& 3) 1))
    (Nat.beq T (pk4 1 2 4 8)) (Nat.beq (R &&& 3) 0)

@[expose] noncomputable def tcand (z2 z4 : Nat) : Nat :=
  pk4 (r0P (pmulP z2 2)) (pmulP z2 2) (r0P (pmulP z4 8)) (pmulP z4 8)

@[expose] noncomputable def tScan (TG TR : Nat) : Bool :=
  allN 4 fun i => allN 4 fun j =>
    tRecOK TG (tcand (16 * i) (16 * j)) (fldN TR 40 1099511627775 (4 * i + j))

@[expose] noncomputable def lcand (v v' : Nat) : Nat := pk4 (r0P (r0P v)) v (r0P (r0P v')) v'

@[expose] noncomputable def lCheap (T L : Nat) : Bool :=
  band (allN 4 fun k => band (Nat.beq (evD L (c4 L k)) (Nat.shiftLeft 1 k))
      (Nat.beq (evD T (c4 L k)) (evD L (c4 T k))))
    (band (anyN 3 fun z => bnot (Nat.beq (evD L (16 * (z + 1))) (16 * (z + 1))))
      (anyN 64 fun x => bnot (Nat.beq (evD T (pmulP (evD L x) (invP x))) (pmulP (evD L x) (invP x)))))

@[expose] noncomputable def lScan (IV T : Nat) (ok : Nat → Bool) : Bool :=
  allN 27 fun c => allN 27 fun d =>
    sb (lcand (fldN IV 6 63 c) (fldN IV 6 63 d)) fun L => bimp (lCheap T L) (ok L)

@[expose] noncomputable def inL (Lp L : Nat) : Bool := anyN 24 fun j => Nat.beq (fldN Lp 24 16777215 j) L

@[expose] noncomputable def scand (u u' : Nat) : Nat := pk4 (r0P (pmulP u 2)) (pmulP u 2) (r0P (pmulP u' 8)) (pmulP u' 8)

@[expose] noncomputable def sCheap (T S : Nat) : Bool :=
  band (allN 4 fun k => band (Nat.beq (evD S (c4 S k)) (Nat.shiftLeft 1 k))
      (Nat.beq (evD T (c4 S k)) (evD S (c4 T k))))
    (band (bnot (Nat.beq S (pk4 1 2 4 8)))
      (allN 64 fun x => bimp (Nat.beq (evD T x) x) (Nat.beq (evD S x) (invP x))))

@[expose] noncomputable def pairOK (RP T S L R : Nat) : Bool :=
  bimp (allN 4 fun k => Nat.beq (evD S (c4 L k)) (evD L (c4 S k)))
    (band (Nat.beq (R &&& 1) 1) (band (pOK ((R >>> 1) &&& 511))
      (band (conjOK ((R >>> 1) &&& 511) (R >>> 12) T T)
        (band (conjOK ((R >>> 1) &&& 511) (R >>> 12) S
            (fldN (fldN RP 48 281474976710655 ((R >>> 10) &&& 3)) 24 16777215 0))
          (conjOK ((R >>> 1) &&& 511) (R >>> 12) L
            (fldN (fldN RP 48 281474976710655 ((R >>> 10) &&& 3)) 24 16777215 1))))))

@[expose] noncomputable def sScan (RP T F Lp K Bp : Nat) : Bool :=
  allN 16 fun a => allN 16 fun b =>
    sb (scand (fldN F 6 63 a) (fldN F 6 63 b)) fun S => bimp (sCheap T S)
      (allN 24 fun j => pairOK RP T S (fldN Lp 24 16777215 j)
        (fldN Bp 40 1099511627775 (24 * fldN K 3 7 (16 * a + b) + j)))

@[expose] noncomputable def fixOK (T F : Nat) : Bool :=
  allN 64 fun u => bimp (Nat.beq (evD T u) u) (anyN 16 fun a => Nat.beq (fldN F 6 63 a) u)

@[expose] noncomputable def invOK (IV : Nat) : Bool :=
  allN 64 fun v => bimp (Nat.beq (pmulP v v) 0)
    (Bool.rec (motive := fun _ => Bool) (anyN 27 fun a => Nat.beq (fldN IV 6 63 a) v) true
      (Nat.beq v 0))

end CFSG.KC.FzUT
