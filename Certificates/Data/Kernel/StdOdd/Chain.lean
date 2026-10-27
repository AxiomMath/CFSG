module

public import Certificates.Data.Kernel.StdOdd.RootOrbit
public import Certificates.Data.Kernel.Misc.E6Std

public section

namespace CFSG.KC.StdOdd.Chain

open CFSG.KC.StdOdd.Orbit

@[expose] noncomputable def forceL (l : List Nat) (k : List Nat → Nat) : Nat :=
  List.rec (motive := fun _ => (List Nat → Nat) → Nat) (fun k => k List.nil)
    (fun x _ ih k => forceN x fun x => ih fun t => k (List.cons x t)) l k

@[expose] noncomputable def forceLB (l : List Nat) (k : List Nat → Bool) : Bool :=
  Nat.beq (forceL l fun t => Bool.rec (motive := fun _ => Nat) 0 1 (k t)) 1

@[expose] noncomputable def forceNL (y : Nat) (k : Nat → List Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) (k (nat_lit 0)) (fun m _ => k (Nat.succ m)) y

@[expose] noncomputable def mapRows (M : Nat) (U : List Nat) : List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun _ ih M => List.cons (rowX M U) (ih (Nat.shiftRight M (nat_lit 156)))) (nat_lit 156) M

@[expose] noncomputable def pairAcc (U V : List Nat) (pk a0 a1 : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ a0 a1 => Nat.lor a0 a1)
    (fun _ ih pk a0 a1 => forceN (Nat.land pk (nat_lit 16383)) fun c =>
      Bool.rec (motive := fun _ => Nat)
      (forceN (Nat.land c (nat_lit 127)) fun a => forceN (Nat.shiftRight c (nat_lit 7)) fun b =>
      forceN (nthN U (Nat.mul 2 a)) fun x0 => forceN (nthN U (Nat.add (Nat.mul 2 a) 1)) fun x1 =>
      forceN (nthN V (Nat.mul 2 b)) fun y0 => forceN (nthN V (Nat.add (Nat.mul 2 b) 1)) fun y1 =>
      forceN (Nat.xor a0 (Nat.xor (Nat.land x0 y0) (Nat.land x1 y1))) fun a0 =>
      forceN (Nat.xor a1 (Nat.xor (Nat.land x0 y1) (Nat.land x1 (Nat.xor y0 y1)))) fun a1 =>
      ih (Nat.shiftRight pk (nat_lit 14)) a0 a1)
      (Nat.lor a0 a1) (Nat.beq c 0)) (nat_lit 6084) pk a0 a1

@[expose] noncomputable def pairNZ (U V : List Nat) (pk : Nat) : Nat :=
  pairAcc U V pk 0 0

@[expose] noncomputable def anyNZ (U V : List Nat) (BL : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun pk _ ih acc => forceN (Nat.lor acc (pairNZ U V pk)) ih) BL (nat_lit 0)

@[expose] noncomputable def neqMask (U V : List Nat) : Nat :=
  List.rec (motive := fun _ => List Nat → Nat → Nat) (fun _ acc => acc)
    (fun x _ ih V acc => List.rec (motive := fun _ => Nat) acc
      (fun y V' _ => forceN (Nat.lor acc (Nat.xor x y)) (ih V')) V) U V (nat_lit 0)

@[expose] noncomputable def andNot (m x : Nat) : Nat := Nat.xor m (Nat.land m x)

@[expose] noncomputable def profMask (M : Nat) (U : List Nat) (w t FP : Nat) (BL : List Nat) :
    Nat :=
  forceL U fun U => forceL (mapRows M U) fun V =>
  forceN (full w) fun F =>
  forceN (Nat.land F (neqMask U V)) fun ne =>
  Bool.rec (motive := fun _ => Nat)
    (forceN (Nat.land ne (pairNZ U V FP)) fun fz =>
     Bool.rec (motive := fun _ => Nat)
      (forceN (andNot ne fz) fun nf =>
       forceN (Nat.land nf (anyNZ U V BL)) fun bz =>
       Bool.rec (motive := fun _ => Nat) (andNot nf bz) bz (Nat.beq t 3))
      fz (Nat.beq t 4))
    (andNot F ne) (Nat.beq t 0)

@[expose] noncomputable def disjL (ms : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun m _ ih acc => andB (Nat.beq (Nat.land m acc) 0) (ih (Nat.lor acc m))) ms (nat_lit 0)

@[expose] noncomputable def orL (ms : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun m _ ih => Nat.lor m ih) ms

@[expose] noncomputable def letterSum (Ms ms U : List Nat) : Nat :=
  List.rec (motive := fun _ => List Nat → Nat) (fun _ => nat_lit 0)
    (fun M _ ih ms => List.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun m ms' _ => Nat.xor (Nat.land m (rowX M U)) (ih ms')) ms) Ms ms

@[expose] noncomputable def shiftRows (Ms : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil
    (fun M _ ih => List.cons (Nat.shiftRight M (nat_lit 156)) ih) Ms

@[expose] noncomputable def stepAux (ms U : List Nat) (o : Nat) (V Ms : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun _ => List.nil)
    (fun x _ ih Ms => List.cons (Nat.xor (andNot x o) (letterSum Ms ms U)) (ih (shiftRows Ms)))
    V Ms

@[expose] noncomputable def stepL (Ms ms U : List Nat) : List Nat :=
  stepAux ms U (orL ms) U Ms

@[expose] noncomputable def walkK (Ms : List Nat) (S : List (List Nat)) (U : List Nat)
    (k : List Nat → Bool) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun U => k U)
    (fun ms _ ih U => andB (andB (Nat.beq (lenN ms) (lenN Ms)) (disjL ms))
      (forceLB (stepL Ms ms U) ih)) S U

@[expose] noncomputable def repl (v w : Nat) : List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun _ ih v => List.cons (Nat.mul (Nat.land v 1) (full w)) (ih (Nat.shiftRight v 1)))
    (nat_lit 156) v

@[expose] noncomputable def neqV (U : List Nat) (v w : Nat) : Nat :=
  forceN (full w) fun F =>
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => Nat.land F acc)
    (fun x _ ih v acc => forceN (Nat.lor acc (Nat.xor x (Nat.mul (Nat.land v 1) F)))
      (ih (Nat.shiftRight v 1))) U v (nat_lit 0)

@[expose] noncomputable def neqPt (U FP : List Nat) (k F : Nat) : Nat :=
  List.rec (motive := fun _ => List Nat → Nat → Nat) (fun _ acc => acc)
    (fun x _ ih FP acc => List.rec (motive := fun _ => Nat) acc
      (fun y FP' _ => forceN (Nat.lor acc (Nat.xor x
        (Nat.mul (Nat.land (Nat.shiftRight y k) 1) F))) (ih FP')) FP) U FP (nat_lit 0)

@[expose] noncomputable def memMask (U FP : List Nat) (s w : Nat) : Nat :=
  forceN (full w) fun F =>
  Nat.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun k ih acc => forceN (Nat.lor acc (andNot F (neqPt U FP k F))) ih) s (nat_lit 0)

@[expose] noncomputable def chunkPl (U : List Nat) (off w : Nat) : List Nat :=
  forceNL (full w) fun F =>
  List.rec (motive := fun _ => List Nat) List.nil
    (fun x _ ih => List.cons (Nat.land (Nat.shiftRight x off) F) ih) U

@[expose] noncomputable def spread (m r k : Nat) : Nat :=
  forceN (Nat.land m (full r)) fun m =>
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i ih => Nat.lor ih (Nat.shiftLeft m (Nat.mul i r))) k

@[expose] noncomputable def spreadS (S : List (List Nat)) (r k : Nat) : List (List Nat) :=
  List.rec (motive := fun _ => List (List Nat)) List.nil
    (fun ms _ ih => List.cons (List.rec (motive := fun _ => List Nat) List.nil
      (fun m _ ih' => List.cons (spread m r k) ih') ms) ih) S

@[expose] noncomputable def catRow (Es : List (List Nat)) (r c : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun E _ ih i => Nat.lor (Nat.shiftLeft (Nat.land (nthN E c) (full r)) (Nat.mul i r))
      (ih (Nat.succ i))) Es 0

@[expose] noncomputable def catPl (Es : List (List Nat)) (r : Nat) : List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun _ ih c => List.cons (catRow Es r c) (ih (Nat.succ c))) (nat_lit 156) 0

@[expose] noncomputable def profAll (X : Nat) (ks ts U : List Nat) (w FP : Nat) (BL : List Nat) :
    Nat :=
  List.rec (motive := fun _ => List Nat → Nat) (fun _ => full w)
    (fun k _ ih ts => List.rec (motive := fun _ => Nat) (full w)
      (fun t ts' _ => forceN (profMask (CFSG.KC.Misc.E6Std.powB X k) U w t FP BL) fun m =>
        Nat.land m (ih ts')) ts) ks ts

@[expose] noncomputable def forceB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k (nat_lit 0)) (fun m _ => k (Nat.succ m)) y

@[expose] noncomputable def popK (x c : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun x => Nat.beq x 0)
    (fun _ ih x => andB (notB (Nat.beq x 0)) (forceB (Nat.land x (Nat.sub x 1)) ih)) c x

@[expose] noncomputable def splitPl (N bw w k : Nat) : List Nat :=
  forceNL (full w) fun F =>
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun _ ih c => List.cons (Nat.land (Nat.shiftRight N (Nat.mul (Nat.mul 8 bw) c)) F)
      (ih (Nat.succ c))) k 0

@[expose] noncomputable def stepsPl (N bw w D m : Nat) : List (List Nat) :=
  Nat.rec (motive := fun _ => Nat → List (List Nat)) (fun _ => List.nil)
    (fun _ ih t => List.cons (splitPl (Nat.shiftRight N (Nat.mul (Nat.mul (Nat.mul 8 bw) m) t))
      bw w m) (ih (Nat.succ t))) D 0

@[expose] noncomputable def vecsRow (vs : List Nat) (c : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun v _ ih r acc =>
      forceN (Nat.lor acc (Nat.shiftLeft (Nat.land (Nat.shiftRight v c) 1) r)) (ih (Nat.succ r)))
    vs 0 0

@[expose] noncomputable def vecsPl (vs : List Nat) : List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun _ ih c => List.cons (vecsRow vs c) (ih (Nat.succ c))) (nat_lit 156) 0

@[expose] noncomputable def eqMaskV (U : List Nat) (v w : Nat) : Nat := andNot (full w) (neqV U v w)

@[expose] noncomputable def allIn (U vs : List Nat) (w : Nat) : Bool :=
  Nat.beq (List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun v _ ih acc => forceN (Nat.land acc (neqV U v w)) ih) vs (full w)) 0

@[expose] noncomputable def refMask (U vs st : List Nat) (w : Nat) : Nat :=
  List.rec (motive := fun _ => List Nat → Nat → Nat) (fun _ acc => acc)
    (fun v _ ih st acc => List.rec (motive := fun _ => Nat) acc
      (fun s st' _ => Bool.rec (motive := fun _ => Nat) (ih st' acc)
        (forceN (Nat.lor acc (eqMaskV U v w)) (ih st')) (Nat.beq s 1)) st) vs st (nat_lit 0)

@[expose] noncomputable def chunkOK (PL : List Nat) (n X : Nat) (ks ts : List Nat) (FP : Nat)
    (BL cnts : List Nat) (q : Nat) : Bool :=
  forceB (Nat.min 262144 (Nat.sub n (Nat.mul q 262144))) fun w =>
  popK (profAll X ks ts (chunkPl PL (Nat.mul q 262144) w) w FP BL) (nthN cnts q)

@[expose] noncomputable def forestOK (FPn WN bw n D : Nat) (Ms : List Nat) (β : Nat) : Bool :=
  forceLB (splitPl FPn bw n 156) fun F => andB (sortOK F n)
    (walkK Ms (stepsPl WN bw n D (lenN Ms)) F fun V => Nat.beq (neqV V β n) 0)

@[expose] noncomputable def candOK (CPn HWn bw s X D b m₀ FP : Nat) (ks1 ts1 ksA tsA BL HL reps st :
    List Nat) : Bool :=
  forceLB (splitPl CPn bw s 156) fun C =>
  andB (andB (sortOK C s) (Nat.beq (profAll X ks1 ts1 C s FP BL) (full s)))
    (forceB (profAll X ksA tsA C s FP BL) fun A =>
      walkK HL (stepsPl HWn bw s D (lenN HL)) C fun V =>
        andB (andB (allIn V reps s) (popK (eqMaskV V b s) m₀))
          (Nat.beq (Nat.land A (andNot (andNot (full s) (eqMaskV V b s)) (refMask V reps st s))) 0))

@[expose] noncomputable def startOK (RN bw D A B b : Nat) (reps : List Nat) : Bool :=
  walkK [A, B] (stepsPl RN bw (lenN reps) D 2) (vecsPl reps) fun V =>
    Nat.beq (neqV V b (lenN reps)) 0

@[expose] noncomputable def fixesOK (M : Nat) (vs : List Nat) (i : Nat) : Bool :=
  forceLB (vecsPl vs) fun U => Nat.beq (Nat.land (neqMask (mapRows M U) U) (full i)) 0

@[expose] noncomputable def transB (M : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ _ acc => acc)
    (fun _ ih c M acc => forceN (Nat.land M (full 156)) fun r =>
      ih (Nat.succ c) (Nat.shiftRight M (nat_lit 156))
        (Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ _ acc => acc)
          (fun _ ih' d r acc => forceN (Nat.lor acc
              (Nat.shiftLeft (Nat.land r 1) (Nat.add (Nat.mul (nat_lit 156) d) c)))
              (ih' (Nat.succ d) (Nat.shiftRight r 1)))
          (nat_lit 156) 0 r acc)) (nat_lit 156) 0 M (nat_lit 0)

@[expose] noncomputable def applyC (MT v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ _ acc => acc)
    (fun _ ih M v acc => forceN (Nat.shiftRight v 1) fun v' =>
      ih (Nat.shiftRight M (nat_lit 156)) v'
        (Bool.rec (motive := fun _ => Nat) (Nat.xor acc (Nat.land M (full 156))) acc
          (Nat.beq (Nat.land v 1) 0))) (nat_lit 156) MT v (nat_lit 0)

end CFSG.KC.StdOdd.Chain

end
