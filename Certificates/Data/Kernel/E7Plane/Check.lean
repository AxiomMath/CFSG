module

public import Init

public section

namespace CFSG.KC.E7Plane

@[expose] noncomputable def andB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) false b a

@[expose] noncomputable def orB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) b true a

@[expose] noncomputable def notB (a : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) true false a

@[expose] noncomputable def impB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) true b a

@[expose] noncomputable def ifB (c t e : Bool) : Bool := Bool.rec (motive := fun _ => Bool) e t c

@[expose] noncomputable def toN (b : Bool) : Nat := Bool.rec (motive := fun _ => Nat) 0 1 b

@[expose] noncomputable def letB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def letN (y : Nat) (k : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def allN (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => andB (f i) ih) n

@[expose] noncomputable def orN (n w : Nat) (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => Nat.lor acc (Nat.shiftLeft (f i) (Nat.mul w i))) n

@[expose] noncomputable def packL {α : Type} (w : Nat) (f : α → Nat) (L : List α) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun x _ ih => Nat.lor (f x) (Nat.shiftLeft ih w)) L

@[expose] noncomputable def lenL {α : Type} (L : List α) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) L

@[expose] noncomputable def fld (X w i : Nat) : Nat :=
  Nat.land (Nat.shiftRight X (Nat.mul w i)) (Nat.sub (Nat.shiftLeft 1 w) 1)

@[expose] noncomputable def f7 (X i : Nat) : Nat := Nat.land (Nat.shiftRight X (Nat.mul 7 i)) 127

@[expose] noncomputable def ln (V i : Nat) : Nat := Nat.land (Nat.shiftRight V (Nat.mul 8 i)) 255

@[expose] noncomputable def rowM : Nat := Nat.sub (Nat.shiftLeft 1 882) 1

@[expose] noncomputable def tupM : Nat := Nat.sub (Nat.shiftLeft 1 49) 1

@[expose] noncomputable def full : Nat := Nat.sub (Nat.shiftLeft 1 2187) 1

@[expose] noncomputable def mask3 : Nat := Nat.sub (Nat.shiftLeft 1 6561) 1

@[expose] noncomputable def b8 : Nat := 2260630401189896

@[expose] noncomputable def ones8 : Nat := 282578800148737

@[expose] noncomputable def idrow : Nat := orN 126 7 fun k => k

@[expose] noncomputable def vecOf (c : Nat) : Nat :=
  orN 7 8 fun j => Nat.land (Nat.shiftRight c (Nat.mul 4 j)) 15

@[expose] noncomputable def vrt (RV : List Nat) : Nat := packL 56 vecOf RV

@[expose] noncomputable def spread (c : Nat) : Nat :=
  orN 7 882 fun i => Nat.land (Nat.shiftRight c (Nat.mul 8 i)) 127

@[expose] noncomputable def imgt (TB : List Nat) : Nat := packL 7 spread TB

@[expose] noncomputable def comp (A B : Nat) : Nat := orN 126 7 fun k => f7 A (f7 B k)

@[expose] noncomputable def compL (A B : Nat) : Nat := letN A fun a => letN B fun b => comp a b

@[expose] noncomputable def rowW (IMGT ID : Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) ID (fun i _ ih => compL (fld IMGT 882 i) ih) w

@[expose] noncomputable def wordsOK (W : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun w _ ih => andB (List.rec (motive := fun _ => Bool) true
      (fun i _ ih' => andB (Nat.blt i 7) ih') w) ih) W

@[expose] noncomputable def apT (R t : Nat) : Nat := orN 7 7 fun j => f7 R (f7 t j)

@[expose] noncomputable def powT (row p : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (Nat.land row tupM) (fun _ ih => letN ih fun t => apT row t)
    (Nat.sub p 1)

@[expose] noncomputable def rot (Q : Nat) : Nat :=
  Nat.land (Nat.lor (Nat.shiftLeft Q 2187) (Nat.shiftRight Q 4374)) mask3

@[expose] noncomputable def rotk (Q k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) Q (fun _ ih => rot ih) (Nat.mod k 3)

@[expose] noncomputable def kstep (Q m s : Nat) : Nat :=
  letN Q fun Q => letN m fun m =>
    Nat.lor Q (Nat.lor (Nat.shiftLeft (rotk Q m) s)
      (Nat.shiftLeft (rotk Q (Nat.mul 2 m)) (Nat.mul 2 s)))

@[expose] noncomputable def res (W j : Nat) : Nat := Nat.mod (ln W j) 3

@[expose] noncomputable def kq (W : Nat) : Nat :=
  letN W fun W =>
    kstep (kstep (kstep (kstep (kstep (kstep (kstep 1 (res W 0) 1) (res W 1) 3) (res W 2) 9)
      (res W 3) 27) (res W 4) 81) (res W 5) 243) (res W 6) 729

@[expose] noncomputable def krt (VRT : Nat) : Nat :=
  orN 126 6561 fun k => kq (Nat.add (fld VRT 56 k) ones8)

@[expose] noncomputable def kqe (KRT : Nat) : Nat := orN 7 6561 fun j => fld KRT 6561 j

@[expose] noncomputable def fix3 (X : Nat) : Nat :=
  Nat.land (Nat.lor X (Nat.lor (Nat.shiftRight X 2187) (Nat.shiftRight X 4374))) full

@[expose] noncomputable def fixm (KRT KQE row : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) full
    (fun j acc => Nat.land acc (letN (Nat.land (fld KRT 6561 (f7 row j)) (fld KQE 6561 j)) fix3)) 7

@[expose] noncomputable def lsum (V : Nat) : Nat :=
  Nat.land (Nat.shiftRight (Nat.mul V ones8) 48) 255

@[expose] noncomputable def posm (VRT : Nat) : Nat :=
  orN 126 1 fun k => toN (Nat.blt 56 (lsum (fld VRT 56 k)))

@[expose] noncomputable def isPos (POS k : Nat) : Bool :=
  Nat.blt 0 (Nat.land POS (Nat.shiftLeft 1 k))

@[expose] noncomputable def orbS (VRT row p k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun _ ih x acc => letN x fun x => ih (f7 row x) (Nat.add acc (fld VRT 56 x))) p k 0

@[expose] noncomputable def zorb (VRT row p k : Nat) : Bool :=
  Nat.beq (orbS VRT row p k) (Nat.mul p b8)

@[expose] noncomputable def zmask (VRT POS row p : Nat) : Nat :=
  orN 126 1 fun k => toN (andB (isPos POS k) (zorb VRT row p k))

@[expose] noncomputable def eT (U V a b : Nat) : Nat :=
  Nat.add (Nat.mul (ln U a) (ln V b)) (Nat.mul (ln U b) (ln V a))

@[expose] noncomputable def edgeS (U V : Nat) : Nat :=
  Nat.add (eT U V 0 2) (Nat.add (eT U V 1 3) (Nat.add (eT U V 2 3) (Nat.add (eT U V 3 4)
    (Nat.add (eT U V 4 5) (eT U V 5 6)))))

@[expose] noncomputable def degS (W : Nat) : Nat :=
  Nat.add (Nat.add (ln W 0) (ln W 2)) (Nat.add (Nat.add (ln W 1) (ln W 3)) (Nat.add
    (Nat.add (ln W 2) (ln W 3)) (Nat.add (Nat.add (ln W 3) (ln W 4)) (Nat.add
      (Nat.add (ln W 4) (ln W 5)) (Nat.add (ln W 5) (ln W 6))))))

@[expose] noncomputable def dot7 (U V : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i acc => Nat.add acc (Nat.mul (ln U i) (ln V i))) 7

@[expose] noncomputable def orthUV (U V : Nat) : Bool :=
  Nat.beq (Nat.add (Nat.mul 2 (dot7 U V)) (Nat.add 128 (Nat.mul 8 (degS (Nat.add U V)))))
    (Nat.add (edgeS U V) (Nat.mul 16 (Nat.add (lsum U) (lsum V))))

@[expose] noncomputable def orthB (VRT a b : Nat) : Bool :=
  letB (fld VRT 56 a) fun U => letB (fld VRT 56 b) fun V => orthUV U V

@[expose] noncomputable def sgnB (VRT row a b : Nat) : Bool :=
  letB (f7 row a) fun c =>
    orB (Nat.beq c b) (Nat.beq (Nat.add (fld VRT 56 c) (fld VRT 56 b)) (Nat.mul 2 b8))

@[expose] noncomputable def triB (VRT row T KB : Nat) : Bool :=
  letB (f7 T 0) fun g0 => letB (f7 T 1) fun g1 => letB (f7 T 2) fun g2 =>
    andB (Nat.beq KB
        (Nat.lor (Nat.lor (Nat.shiftLeft 1 g0) (Nat.shiftLeft 1 g1)) (Nat.shiftLeft 1 g2)))
      (andB (orthB VRT g0 g1)
        (andB (sgnB VRT row g0 g1) (andB (sgnB VRT row g1 g2) (sgnB VRT row g2 g0))))

@[expose] noncomputable def rkf (KRT FLs m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun k acc => Nat.lor acc (letN (fld KRT 6561 k) fun Q =>
    Nat.rec (motive := fun _ => Nat) 0 (fun c acc' => Nat.lor acc'
      (Nat.shiftLeft (Nat.land (Nat.shiftRight Q (fld FLs 12 c)) 1)
        (Nat.add (Nat.mul 126 c) k))) m))
    126

@[expose] noncomputable def flMask (FLs m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun c acc => Nat.lor acc (Nat.shiftLeft 1 (fld FLs 12 c))) m

@[expose] noncomputable def hardB (VRT KRT POS row p F H : Nat) : Bool :=
  letB (Nat.land H 63) fun m => letB (Nat.shiftRight H 6) fun FLs =>
    letB (Nat.shiftRight FLs (Nat.mul 12 m)) fun TRI =>
      andB (Nat.beq (flMask FLs m) F)
        (letB (rkf KRT FLs m) fun RKF => letB (zmask VRT POS row p) fun ZM =>
          allN m fun c => allN m fun d =>
            letB (Nat.land (Nat.land (fld RKF 126 c) (fld RKF 126 d)) POS) fun KB =>
              orB (Nat.blt 0 (Nat.land KB ZM))
                (triB VRT row (fld TRI 21 (Nat.add (Nat.mul c m) d)) KB))

@[expose] noncomputable def easyB (VRT KRT POS row p F x : Nat) : Bool :=
  andB (Nat.blt x 126) (andB (isPos POS x) (andB (zorb VRT row p x)
    (Nat.beq (Nat.land F (Nat.xor full (Nat.land (fld KRT 6561 x) full))) 0)))

@[expose] noncomputable def recB (VRT KRT KQE POS GT RT KT DT ID p n i0 ng i prev r : Nat) : Bool :=
  letB (Nat.land r rowM) fun row => letB (Nat.shiftRight r 882) fun e =>
    letB (Nat.land row tupM) fun t =>
      andB (Nat.blt prev t) <|
      andB (ifB (Nat.beq i i0) (Nat.beq row ID)
        (letB (Nat.land e 2047) fun q => letB (Nat.land (Nat.shiftRight e 11) 15) fun l =>
          andB (Nat.blt l ng) (andB (Nat.blt q n)
            (andB (Nat.beq (Nat.land (Nat.shiftRight e 15) 511) (Nat.succ (fld DT 9 q)))
              (Nat.beq row (compL (fld GT 882 l) (fld RT 882 q))))))) <|
      andB (letB (Nat.shiftRight r 913) fun cl => allN ng fun l =>
        letB (Nat.land (Nat.shiftRight cl (Nat.mul 11 l)) 2047) fun c =>
          andB (Nat.blt c n) (Nat.beq (fld KT 49 c) (letN (fld GT 882 l) fun g => apT g t))) <|
      impB (andB (notB (Nat.beq t (Nat.land ID tupM))) (Nat.beq (powT row p) (Nat.land ID tupM)))
        (letB (fixm KRT KQE row) fun F => letB (Nat.land (Nat.shiftRight e 24) 127) fun x =>
          ifB (Nat.beq x 127) (hardB VRT KRT POS row p F (Nat.shiftRight r 1088))
            (easyB VRT KRT POS row p F x))

@[expose] noncomputable def walkB (VRT KRT KQE POS GT RT KT DT ID p n i0 ng : Nat) (R : List Nat) :
    Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool) (fun i _ => Nat.beq i n)
    (fun r _ ih i prev => andB (recB VRT KRT KQE POS GT RT KT DT ID p n i0 ng i prev r)
      (letB (Nat.succ i) fun i' => ih i' (Nat.land r tupM))) R

@[expose] noncomputable def sylK (RV TB : List Nat) (p n i0 : Nat) (W : List (List Nat))
    (R : List Nat) : Bool :=
  letB (vrt RV) fun VRT => letB (imgt TB) fun IMGT => letB idrow fun ID =>
  letB (krt VRT) fun KRT => letB (kqe KRT) fun KQE => letB (posm VRT) fun POS =>
  letB (packL 882 (rowW IMGT ID) W) fun GT => letB (lenL W) fun ng =>
  letB (packL 882 (fun r => Nat.land r rowM) R) fun RT =>
  letB (packL 49 (fun r => Nat.land r tupM) R) fun KT =>
  letB (packL 9 (fun r => Nat.land (Nat.shiftRight r 897) 511) R) fun DT =>
    andB (wordsOK W) (andB (Nat.blt i0 n) (andB (Nat.blt ng 16)
      (walkB VRT KRT KQE POS GT RT KT DT ID p n i0 ng R 0 0)))

end CFSG.KC.E7Plane

end
