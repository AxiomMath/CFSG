module

public section

namespace Certificates.A3E6K

@[expose] noncomputable def andB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) false b a

@[expose] noncomputable def notB (b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) true false b

@[expose] noncomputable def fld (x w i : Nat) : Nat :=
  Nat.land (Nat.shiftRight x (Nat.mul w i)) (Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1))

@[expose] noncomputable def bitB (x n : Nat) : Bool :=
  Nat.blt (nat_lit 0) (Nat.land x (Nat.shiftLeft (nat_lit 1) n))

@[expose] noncomputable def letNB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k (nat_lit 0)) (fun m _ => k (Nat.succ m)) y

@[expose] noncomputable def allN (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => andB (f k) ih) n

@[expose] noncomputable def sumN (n : Nat) (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun k ih => Nat.add ih (f k)) n

@[expose] noncomputable def maskN (n : Nat) (f : Nat → Bool) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k ih => Nat.lor ih (Bool.rec (motive := fun _ => Nat) (nat_lit 0)
      (Nat.shiftLeft (nat_lit 1) k) (f k))) n

@[expose] noncomputable def popc (x n : Nat) : Nat :=
  sumN n fun k => Nat.land (Nat.shiftRight x k) (nat_lit 1)

@[expose] noncomputable def hd (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun x _ _ => x) l

@[expose] noncomputable def nth (l : List Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun x _ ih i => Nat.rec (motive := fun _ => Nat) x (fun j _ => ih j) i) l i

@[expose] noncomputable def tl (l : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun _ t _ => t) l

@[expose] noncomputable def nthL (l : List (List Nat)) (i : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun x _ ih i => Nat.rec (motive := fun _ => List Nat) x (fun j _ => ih j) i) l i

@[expose] noncomputable def nthLL (l : List (List (List Nat))) (i : Nat) : List (List Nat) :=
  List.rec (motive := fun _ => Nat → List (List Nat)) (fun _ => [])
    (fun x _ ih i => Nat.rec (motive := fun _ => List (List Nat)) x (fun j _ => ih j) i) l i

@[expose] noncomputable def nthF (l : List (List (List (List Nat)))) (i : Nat) :
    List (List (List Nat)) :=
  List.rec (motive := fun _ => Nat → List (List (List Nat))) (fun _ => [])
    (fun x _ ih i => Nat.rec (motive := fun _ => List (List (List Nat))) x (fun j _ => ih j) i) l i

@[expose] noncomputable def cd (c j : Nat) : Nat :=
  Nat.land (Nat.shiftRight c (Nat.mul (nat_lit 4) j)) (nat_lit 15)

@[expose] noncomputable def rc (R k : Nat) : Nat := fld R (nat_lit 24) k

@[expose] noncomputable def row72 (T i : Nat) : Nat := fld T (nat_lit 72) i

@[expose] noncomputable def rel (T i k : Nat) : Bool :=
  bitB T (Nat.add (Nat.mul (nat_lit 72) i) k)

@[expose] noncomputable def eS (x y a b : Nat) : Nat :=
  Nat.add (Nat.add (cd x a) (cd y b)) (Nat.add (cd x b) (cd y a))

@[expose] noncomputable def eP (x y a b : Nat) : Nat :=
  Nat.add (Nat.add (Nat.mul (cd x a) (cd y b)) (Nat.mul (cd x b) (cd y a))) (nat_lit 128)

@[expose] noncomputable def fpos (x y : Nat) : Nat :=
  Nat.add
    (Nat.mul (nat_lit 2) (sumN (nat_lit 6) fun j => Nat.add (Nat.mul (cd x j) (cd y j)) (nat_lit 64)))
    (Nat.mul (nat_lit 8) (Nat.add (Nat.add (Nat.add (Nat.add (eS x y (nat_lit 0) (nat_lit 2))
      (eS x y (nat_lit 1) (nat_lit 3))) (eS x y (nat_lit 2) (nat_lit 3)))
      (eS x y (nat_lit 3) (nat_lit 4))) (eS x y (nat_lit 4) (nat_lit 5))))

@[expose] noncomputable def fneg (x y : Nat) : Nat :=
  Nat.add (Nat.mul (nat_lit 16) (sumN (nat_lit 6) fun j => Nat.add (cd x j) (cd y j)))
    (Nat.add (Nat.add (Nat.add (Nat.add (eP x y (nat_lit 0) (nat_lit 2))
      (eP x y (nat_lit 1) (nat_lit 3))) (eP x y (nat_lit 2) (nat_lit 3)))
      (eP x y (nat_lit 3) (nat_lit 4))) (eP x y (nat_lit 4) (nat_lit 5)))

@[expose] noncomputable def formZ (x y : Nat) : Bool := Nat.beq (fpos x y) (fneg x y)

@[expose] noncomputable def formM (x y : Nat) : Bool :=
  Nat.beq (Nat.add (fpos x y) (nat_lit 1)) (fneg x y)

@[expose] noncomputable def rootsOK (R : Nat) (C : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun k => Nat.beq k (nat_lit 72))
    (fun c _ ih k => andB (Nat.beq (rc R k) c) (ih (Nat.succ k))) C (nat_lit 0)

@[expose] noncomputable def masksAt (R Z N i : Nat) : Bool :=
  andB (Nat.beq (row72 Z i) (maskN (nat_lit 72) fun k => formZ (rc R i) (rc R k)))
    (Nat.beq (row72 N i) (maskN (nat_lit 72) fun k => formM (rc R i) (rc R k)))

@[expose] noncomputable def headsM (L : List (List Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun e _ ih => Nat.lor ih (Nat.shiftLeft (nat_lit 1) (hd e))) L

@[expose] noncomputable def resM (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x _ ih => Nat.lor ih (Nat.shiftLeft (nat_lit 1) (Nat.mod x (nat_lit 72)))) l

@[expose] noncomputable def inFrames (P i j : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun x _ ih => andB (andB (Nat.blt (Nat.div x (nat_lit 72)) (nat_lit 270))
      (andB (bitB (fld P (nat_lit 72) (Nat.div x (nat_lit 72))) i)
        (andB (bitB (fld P (nat_lit 72) (Nat.div x (nat_lit 72))) j)
          (bitB (fld P (nat_lit 72) (Nat.div x (nat_lit 72))) (Nat.mod x (nat_lit 72)))))) ih) l

@[expose] noncomputable def coverAt (Z N P : Nat) (row : List (List Nat)) (i : Nat) : Bool :=
  andB (Nat.beq (headsM row) (row72 N i))
    (List.rec (motive := fun _ => Bool) true
      (fun e _ ih => andB (andB
        (Nat.beq (resM (tl e)) (Nat.land (row72 N (hd e)) (row72 Z i)))
        (inFrames P i (hd e) (tl e))) ih) row)

@[expose] noncomputable def cvRow (c₀ c₁ : List (List (List Nat))) (i : Nat) : List (List Nat) :=
  Bool.rec (motive := fun _ => List (List Nat)) (nthLL c₁ (Nat.sub i (nat_lit 36))) (nthLL c₀ i)
    (Nat.blt i (nat_lit 36))

@[expose] noncomputable def hdH (f : List (List (List Nat))) : List Nat := nthL (nthLL f 0) 0

@[expose] noncomputable def colc (R : Nat) (h : List Nat) (k : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (rc R (nth h k)) (nth h (nat_lit 5)) (Nat.beq k (nat_lit 5))

@[expose] noncomputable def bP (R : Nat) (h : List Nat) : Nat :=
  sumN (nat_lit 6) fun k => Nat.shiftLeft (colc R h k) (Nat.mul (nat_lit 24) k)

@[expose] noncomputable def b24 (Bp k i : Nat) : Nat :=
  Nat.mod (Nat.add (cd (fld Bp (nat_lit 24) k) i) (nat_lit 16)) (nat_lit 24)

@[expose] noncomputable def aX (A k j : Nat) : Nat :=
  fld A (nat_lit 8) (Nat.add (Nat.mul (nat_lit 6) k) j)

@[expose] noncomputable def aE (A k j : Nat) : Nat :=
  Nat.mod (Nat.add (aX A k j) (nat_lit 8)) (nat_lit 24)

@[expose] noncomputable def structOK (R Z N P : Nat) (h : List Nat) (t : Nat) : Bool :=
  andB (allN (nat_lit 5) fun k => Nat.blt (nth h k) (nat_lit 72))
  (andB (andB (rel N (nth h 0) (nth h 1)) (andB (rel N (nth h 1) (nth h 2))
    (andB (rel Z (nth h 0) (nth h 2)) (rel Z (nth h 3) (nth h 4)))))
  (andB (andB (Nat.beq (popc (Nat.land (row72 Z (nth h 0)) (Nat.land (row72 Z (nth h 1))
      (row72 Z (nth h 2)))) (nat_lit 72)) (nat_lit 4))
    (andB (andB (rel Z (nth h 0) (nth h 3)) (andB (rel Z (nth h 1) (nth h 3))
      (rel Z (nth h 2) (nth h 3))))
     (andB (rel Z (nth h 0) (nth h 4)) (andB (rel Z (nth h 1) (nth h 4))
      (rel Z (nth h 2) (nth h 4))))))
  (andB (andB (Nat.beq (popc (Nat.land (row72 Z (nth h 3)) (row72 Z (nth h 4))) (nat_lit 72))
      (nat_lit 12))
    (Nat.beq (fld P (nat_lit 72) t) (Nat.land (row72 Z (nth h 3)) (row72 Z (nth h 4)))))
  (andB (allN (nat_lit 5) fun k => formZ (nth h (nat_lit 5)) (rc R (nth h k)))
    (letNB (bP R h) fun Bp => allN (nat_lit 6) fun i => allN (nat_lit 6) fun j =>
      Nat.beq (Nat.add (sumN (nat_lit 6) fun k =>
          Nat.mul (cd (fld Bp (nat_lit 24) k) i) (aX (nth h (nat_lit 6)) k j)) (nat_lit 3072))
        (Nat.add (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 8) (Nat.beq i j))
          (Nat.add (Nat.mul (nat_lit 64) (sumN (nat_lit 6) fun k => cd (fld Bp (nat_lit 24) k) i))
            (Nat.mul (nat_lit 8) (sumN (nat_lit 6) fun k => aX (nth h (nat_lit 6)) k j)))))))))

@[expose] noncomputable def dbit (d n : Nat) : Nat := Nat.land (Nat.shiftRight d n) (nat_lit 1)

@[expose] noncomputable def sg (e x : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) x (Nat.sub (nat_lit 24) (Nat.mod x (nat_lit 24)))
    (Nat.beq e (nat_lit 1))

@[expose] noncomputable def yAt (Bp d : Nat) (u : Nat → Nat) (i : Nat) : Nat :=
  Nat.mod (Nat.add (Nat.add (Nat.add (Nat.mul (b24 Bp (nat_lit 0) i) (u (nat_lit 0)))
      (Nat.mul (b24 Bp (nat_lit 1) i) (u (nat_lit 1))))
      (Nat.add (Nat.mul (b24 Bp (nat_lit 2) i) (u (nat_lit 2)))
        (sg (dbit d (nat_lit 2))
          (Nat.mul (b24 Bp (Nat.add (nat_lit 3) (dbit d (nat_lit 3))) i) (u (nat_lit 3))))))
    (Nat.add (sg (dbit d (nat_lit 1))
        (Nat.mul (b24 Bp (Nat.sub (nat_lit 4) (dbit d (nat_lit 3))) i) (u (nat_lit 4))))
      (sg (dbit d (nat_lit 0)) (Nat.mul (b24 Bp (nat_lit 5) i) (u (nat_lit 5))))))
    (nat_lit 24)

@[expose] noncomputable def uA (A : Nat) (w : Nat → Nat) (k : Nat) : Nat :=
  Nat.mod (sumN (nat_lit 6) fun j => Nat.mul (aE A k j) (w j)) (nat_lit 24)

@[expose] noncomputable def rrP : Nat := nat_lit 2385204

@[expose] noncomputable def rrT (tw : Bool) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 545275912) (nat_lit 285220880) tw

@[expose] noncomputable def tag0 (Bp A d : Nat) (tg : List Nat) : Bool :=
  andB (andB (Nat.blt (nth tg 1) (nat_lit 6)) (Nat.blt (nth tg 2) (nat_lit 6)))
    (notB (Nat.beq (Nat.mod (yAt Bp d (fun k => aE A k (nth tg 2)) (nth tg 1)) (nat_lit 8))
      (nat_lit 0)))

@[expose] noncomputable def tag1 (tw : Bool) (Bp A d : Nat) : Bool :=
  notB (allN (nat_lit 6) fun i =>
    Nat.beq (yAt Bp d (uA A fun j => fld rrP (nat_lit 4) j) i) (fld (rrT tw) (nat_lit 5) i))

@[expose] noncomputable def tag2 (R Z : Nat) (h : List Nat) (Bp A d : Nat) (tg : List Nat) :
    Bool :=
  andB (Nat.blt (nth tg 10) (nat_lit 72))
  (andB (notB (andB (rel Z (nth h 3) (nth tg 10)) (rel Z (nth h 4) (nth tg 10))))
  (andB (notB (andB (rel Z (nth h 0) (nth tg 10)) (andB (rel Z (nth h 1) (nth tg 10))
      (rel Z (nth h 2) (nth tg 10)))))
    (allN (nat_lit 6) fun i =>
      Nat.beq (Nat.mod (Nat.add (Nat.add
          (Nat.div (yAt Bp d (uA A fun j => nth tg (Nat.add (nat_lit 1) j)) i) (nat_lit 8))
          (nth tg (Nat.add (nat_lit 1) i)))
        (Nat.add (Nat.add
          (Nat.mul (nth tg 7) (Nat.add (cd (fld Bp (nat_lit 24) (nat_lit 0)) i) (nat_lit 1)))
          (Nat.mul (nth tg 8) (Nat.add (cd (fld Bp (nat_lit 24) (nat_lit 1)) i) (nat_lit 1))))
          (Nat.mul (nth tg 9) (Nat.add (cd (fld Bp (nat_lit 24) (nat_lit 2)) i) (nat_lit 1)))))
        (nat_lit 3))
      (Nat.mod (Nat.add (cd (rc R (nth tg 10)) i) (nat_lit 1)) (nat_lit 3)))))

@[expose] noncomputable def tagOK (tw : Bool) (R Z : Nat) (h : List Nat) (Bp d : Nat)
    (tg : List Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool)
        (andB (Nat.beq (hd tg) (nat_lit 3)) (andB (notB tw) (Nat.beq (Nat.land d (nat_lit 9)) (nat_lit 0))))
        (andB tw (tag2 R Z h Bp (nth h (nat_lit 6)) d tg)) (Nat.beq (hd tg) (nat_lit 2)))
      (tag1 tw Bp (nth h (nat_lit 6)) d) (Nat.beq (hd tg) (nat_lit 1)))
    (tag0 Bp (nth h (nat_lit 6)) d tg) (Nat.beq (hd tg) (nat_lit 0))

@[expose] noncomputable def tagsOK (tw : Bool) (R Z : Nat) (h : List Nat) (tags : List (List Nat)) :
    Bool :=
  letNB (bP R h) fun Bp =>
    List.rec (motive := fun _ => Nat → Bool) (fun d => Nat.beq d (nat_lit 16))
      (fun tg _ ih d => andB (tagOK tw R Z h Bp d tg) (ih (Nat.succ d))) tags (nat_lit 0)

@[expose] noncomputable def framesStruct (R Z N P : Nat) (L : List (List (List (List Nat))))
    (t₀ t₁ : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun t => Nat.beq t t₁)
    (fun f _ ih t => andB (structOK R Z N P (hdH f) t) (ih (Nat.succ t))) L t₀

@[expose] noncomputable def framesTags (tw : Bool) (R Z : Nat) (L : List (List (List (List Nat)))) :
    Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun f _ ih => andB (tagsOK tw R Z (hdH f)
      (nthLL f (Bool.rec (motive := fun _ => Nat) (nat_lit 2) (nat_lit 1) tw))) ih) L

end Certificates.A3E6K

end
