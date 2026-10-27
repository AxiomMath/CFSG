module

public import Certificates.Data.Kernel.HeAutK
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Q47Tests
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeSylowTests

public section

namespace CFSG.KC.Q47K

open CFSG.KC.Enum CFSG.KS CFSG.KC.HexaK CFSG.KC.HeAutK
open CFSG.KLie.CT (anyN sumN andB orB notB)

@[expose] noncomputable def bn (b : Bool) : Nat := Bool.rec (motive := fun _ => Nat) 0 1 b

@[expose] noncomputable def maskOf (B : Array Nat) : Nat :=
  B.toList.foldr (fun b acc => Nat.lor acc (Nat.shiftLeft 1 b)) 0

@[expose] noncomputable def mapsK (t : Nat) (A : Array Nat) (m : Nat) : Bool :=
  A.toList.all fun a => bitK m (pg 7 (mask 7) t a)

@[expose] noncomputable def swapK (W1 W2 : Array Nat) (t : Nat) : Bool :=
  CFSG.KLie.CT.orB (CFSG.KLie.CT.andB (mapsK t W1 (maskOf W1)) (mapsK t W2 (maskOf W2)))
    (CFSG.KLie.CT.andB (mapsK t W1 (maskOf W2)) (mapsK t W2 (maskOf W1)))

@[expose] noncomputable def ord3 (t : Nat) : Bool :=
  CFSG.KLie.CT.andB (Nat.beq (pw 64 7 t 3) (pidn 64 7)) (CFSG.KLie.CT.notB (Nat.beq t (pidn 64 7)))

@[expose] noncomputable def strictL (y : Nat) (k : Nat → List Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def memK (L : List Nat) (x : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun y _ ih => CFSG.KLie.CT.orB (Nat.beq x y) ih) L

@[expose] noncomputable def runStep (n w ng : Nat) (G : Nat → Nat) (x : Nat) (pts : List Nat) :
    List Nat :=
  Nat.rec (motive := fun _ => List Nat) pts (fun k acc => strictL (mul n w (G k) x) fun y =>
    Bool.rec (motive := fun _ => List Nat) (acc ++ [y]) acc (memK acc y)) ng

@[expose] noncomputable def runK (n w ng : Nat) (G : Nat → Nat) (fuel : Nat) : List Nat :=
  (Nat.rec (motive := fun _ => List Nat × Nat) ([pidn n w], 0)
    (fun _ st => Bool.rec (motive := fun _ => List Nat × Nat) st
      (runStep n w ng G (st.1.getD st.2 0) st.1, Nat.succ st.2) (Nat.blt st.2 st.1.length))
    fuel).1

@[expose] noncomputable def clsAt (gE : Nat) (GE : Nat → Nat) (TE : List Nat) (T1 T2 : List Nat)
    (gD : Nat) (GD : Nat → Nat) (w : Nat) : Bool :=
  CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (allN gE fun e => memK TE (conj 64 7 w (GE e))))
    (CFSG.KLie.CT.orB (memK T1 w) (CFSG.KLie.CT.orB (memK T2 w)
      (Nat.beq (runK 64 7 (Nat.succ gD) (fun k => nIf(Nat.blt k gD, GD k, w)) 200).length 96)))

structure Cls where
  gE : Nat
  GE : Nat → Nat
  TE : List Nat
  T1 : List Nat
  T2 : List Nat
  gD : Nat
  GD : Nat → Nat

@[expose] noncomputable def clsC (c : Cls) (w : Nat) : Bool :=
  clsAt c.gE c.GE c.TE c.T1 c.T2 c.gD c.GD w

@[expose] noncomputable def okT (W1 W2 : Array Nat) (L30 : List (Array Nat)) (cs : List Cls)
    (t : Nat) : Bool :=
  CFSG.KLie.CT.andB (CFSG.KLie.CT.andB ((List.range 30).any fun j => mapsK t W1 (maskOf (L30.getD j #[])))
      ((List.range 30).any fun j => mapsK t W2 (maskOf (L30.getD j #[]))))
    (CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (ord3 t)) (cs.all fun c => clsC c t))

@[expose] noncomputable def oStep (W1 W2 : Array Nat) (L30 : List (Array Nat)) (cs : List Cls)
    (t st : Nat) : Nat :=
  strictN t fun t => Nat.add st (Nat.add (bn (mapsK t W1 (maskOf W1)))
    (Nat.add (Nat.mul 65536 (bn (mapsK t W2 (maskOf W2))))
      (Nat.add (Nat.mul 4294967296 (bn (swapK W1 W2 t)))
        (Nat.mul 281474976710656 (bn (CFSG.KLie.CT.notB (okT W1 W2 L30 cs t)))))))

@[expose] noncomputable def oFold (SZ : Nat → Nat) (TR : Nat → Nat → Nat) (F : Nat → Nat → Nat) :
    Nat → Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ p st => F p st)
    (fun _ ih k p st => foldN (SZ k) (fun j st' => strictN (mul 64 7 p (TR k j)) fun q =>
      ih (Nat.succ k) q st') st)

@[expose] noncomputable def oBlock (SZ : Nat → Nat) (TR : Nat → Nat → Nat) (W1 W2 : Array Nat)
    (L30 : List (Array Nat)) (cs : List Cls) (s : Nat) : Nat :=
  oFold SZ TR (oStep W1 W2 L30 cs) 5 1 (TR 0 s) 0

@[expose] noncomputable def transYK (LY : List Nat) (W : Array Nat) : Bool :=
  W.toList.all fun w => CFSG.KLie.CT.orB (Nat.beq w 0) (LY.any fun y => Nat.beq (pg 7 (mask 7) y W[1]!) w)

@[expose] noncomputable def orbK (LY : List Nat) (Orb : List (Nat × Nat))
    (OrbRep L30 : List (Array Nat)) : Bool :=
  (List.range 30).all fun j => (fun p : Nat × Nat => CFSG.KLie.CT.orB (Nat.ble 4 p.1)
    (CFSG.KLie.CT.andB (Nat.blt p.2 LY.length)
      (mapsK (LY.getD p.2 0) (OrbRep.getD p.1 #[]) (maskOf (L30.getD j #[])))))
    (Orb.getD j (0, 0))

@[expose] noncomputable def stabYK (gY : Nat) (GY : Nat → Nat) (gU : Nat) (GU : Nat → Nat)
    (LU : List Nat) : Bool :=
  allN gY fun y => allN gU fun u => memK LU (conj 64 7 (GY y) (GU u))

@[expose] noncomputable def evalK (L : Nat → Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (pidn 64 7) (fun l _ acc => strictN acc fun acc =>
    mul 64 7 (L (Nat.sub l 1)) acc) w

@[expose] noncomputable def witL (GY : Nat → Nat) (h : Nat) (k : Nat) : Nat :=
  nIf(Nat.blt k 2, GY k, h)

@[expose] noncomputable def witK (GY : Nat → Nat) (g u : Nat) (ws : List (List Nat)) : Bool :=
  strictB (mul 64 7 g u) fun h =>
    Nat.beq (runK 64 7 ws.length (fun k => evalK (witL GY h) (ws.getD k [])) 100).length 32

@[expose] noncomputable def matOf (d m : Nat) : List Nat :=
  (List.range (d * d)).map fun e => pg 4 15 m e

@[expose] noncomputable def findK (N : Nat) (T S : Nat → Nat) (p : Nat) : Nat :=
  S (Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun lo _ => lo)
    (fun _ ih lo hi => strictN (Nat.div (Nat.add lo hi) 2) fun mid =>
      nIf(Nat.blt p (T (S mid)), ih lo mid, ih mid hi)) 12 0 N)

@[expose] noncomputable def key3K (t : Nat) : Nat :=
  Nat.add (pg 7 (mask 7) t 1) (Nat.add (Nat.mul 64 (pg 7 (mask 7) t 4)) (Nat.mul 4096 (pg 7 (mask 7) t 16)))

@[expose] noncomputable def tableHeadK (N : Nat) (T : Nat → Nat) (MP : Nat → Nat) (d : Nat)
    (scal : List Nat → Bool) : Bool :=
  CFSG.KLie.CT.andB (allN N fun i => allN i fun j => CFSG.KLie.CT.notB (Nat.beq (key3K (T i)) (key3K (T j))))
  (CFSG.KLie.CT.andB (Nat.beq (T 0) (pidn 64 7))
    (allN N fun i => CFSG.KLie.CT.orB (Nat.beq i 0) (CFSG.KLie.CT.notB (scal (matOf d (MP i))))))

@[expose] noncomputable def mulMK (d p a b : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun e acc => Nat.lor acc (Nat.shiftLeft
    (Nat.mod (sumN d fun k => Nat.mul (pg 4 15 a (Nat.add (Nat.mul (Nat.div e d) d) k))
      (pg 4 15 b (Nat.add (Nat.mul k d) (Nat.mod e d)))) p) (Nat.mul 4 e))) (Nat.mul d d)

@[expose] noncomputable def projK (a b : Nat) : Bool :=
  anyN 7 fun l => CFSG.KLie.CT.andB (CFSG.KLie.CT.notB (Nat.beq l 0))
    (allN 4 fun e => Nat.beq (pg 4 15 a e) (Nat.mod (Nat.mul (pg 4 15 b e) l) 7))

@[expose] noncomputable def tableRowK (N : Nat) (T S : Nat → Nat) (MP : Nat → Nat) (d p : Nat)
    (mulOK : Nat → Nat → Bool) (i : Nat) : Bool :=
  allN N fun j => strictB (mul 64 7 (T i) (T j)) fun q =>
    CFSG.KLie.CT.andB (Nat.beq (T (findK N T S q)) q)
      (mulOK (mulMK d p (MP i) (MP j)) (MP (findK N T S q)))

@[expose] noncomputable def addK (t : Nat) : Bool :=
  allN 64 fun u => allN 64 fun v =>
    Nat.beq (pg 7 (mask 7) t (Nat.xor u v)) (Nat.xor (pg 7 (mask 7) t u) (pg 7 (mask 7) t v))

@[expose] noncomputable def repK (n w : Nat) (REP : Nat → Nat) (NQ : Nat) (TQ : Nat → Nat)
    (z : Nat) (form : Array Nat) : Bool :=
  CFSG.KLie.CT.andB (Nat.beq (REP 0) (pidn n w))
  (CFSG.KLie.CT.andB (allN 64 fun v => inL NQ TQ (REP v))
  (CFSG.KLie.CT.andB (allN 64 fun u => allN 64 fun v => strictB (mul n w (REP u) (REP v)) fun q =>
      CFSG.KLie.CT.orB (Nat.beq q (REP (Nat.xor u v))) (Nat.beq q (mul n w (REP (Nat.xor u v)) z)))
  (CFSG.KLie.CT.andB (allN NQ fun k => strictB (TQ k) fun x =>
      anyN 64 fun v => CFSG.KLie.CT.orB (Nat.beq x (REP v)) (Nat.beq x (mul n w (REP v) z)))
    (allN 64 fun v => strictB (mul n w (REP v) (REP v)) fun q =>
      CFSG.KLie.CT.orB (CFSG.KLie.CT.andB (Nat.beq q (pidn n w)) (Nat.beq form[v]! 0))
        (CFSG.KLie.CT.andB (Nat.beq q z) (Nat.beq form[v]! 1))))))

@[expose] noncomputable def imgK (n w : Nat) (REP : Nat → Nat) (z : Nat) (g : Nat) (G Dm : Nat → Nat) :
    Bool :=
  allN g fun k => allN 64 fun v => strictB (conj n w (G k) (REP v)) fun q =>
    strictB (pg 7 (mask 7) (Dm k) v) fun dv =>
      CFSG.KLie.CT.orB (Nat.beq q (REP dv)) (Nat.beq q (mul n w (REP dv) z))

@[expose] noncomputable def modelYK (n w : Nat) (gNE : Nat) (GNE : Nat → Nat) (NX : Nat)
    (TX : Nat → Nat) (gE : Nat) (GE : Nat → Nat) (NE : Nat) (TE : Nat → Nat) (gF : Nat)
    (GF : Nat → Nat) (NF : Nat) (TF : Nat → Nat) (gD : Nat) (GD : Nat → Nat)
    (LL : Nat → List Nat) (gY : Nat) (GY : Nat → Nat) (CP : Nat → Nat) (LK : Nat → List Nat) :
    Bool :=
  CFSG.KLie.CT.andB (allN gNE fun k => inL NX TX (GNE k))
  (CFSG.KLie.CT.andB (allN gNE fun k => allN gE fun q => inL NE TE (conj n w (GNE k) (GE q)))
  (CFSG.KLie.CT.andB (allN gNE fun k => allN gF fun q => inL NF TF (conj n w (GNE k) (GF q)))
  (CFSG.KLie.CT.andB (allN 4 fun l => allN gD fun k => memK (LL l) (GD k))
    (allN 4 fun c => allN gY fun y => memK (LK c) (conj 64 7 (CP c) (GY y))))))

@[expose] noncomputable def refPK (LY : List Nat) (GY GU1 GU2 : Nat → Nat) (LU1 LU2 : List Nat)
    (GN : Nat → Nat) (NN : Nat) (TN : Nat → Nat) (W1 W2 : Array Nat) (Orb : List (Nat × Nat))
    (OrbRep L30 : List (Array Nat)) : Bool :=
  CFSG.KLie.CT.andB (transYK LY W1) (CFSG.KLie.CT.andB (transYK LY W2) (CFSG.KLie.CT.andB (orbK LY Orb OrbRep L30)
  (CFSG.KLie.CT.andB (stabYK 2 GY 3 GU1 LU1) (CFSG.KLie.CT.andB (stabYK 2 GY 3 GU2 LU2)
  (CFSG.KLie.CT.andB (allN 2 fun k => inL NN TN (GY k)) (allN 2 fun k => swapK W1 W2 (GN k)))))))

@[expose] noncomputable def witsK (GY G1 G2 : Nat → Nat) (LU1 LU2 : List Nat)
    (wit : List (List (List Nat))) : Bool :=
  allN 2 fun s => allN 4 fun k => allN 8 fun j =>
    witK GY (nIf(Nat.beq s 0, G1 k, G2 k)) (Bool.rec (motive := fun _ => Nat) (LU2.getD j 0)
      (LU1.getD j 0) (Nat.beq s 0)) (wit.getD ((s * 4 + k) * 8 + j) [])

@[expose] noncomputable def bcK (BC : Nat → Nat) : Bool :=
  CFSG.KLie.CT.andB (Nat.beq (sumN 35 fun s => Nat.land (BC s) 65535) 1344)
  (CFSG.KLie.CT.andB (Nat.beq (sumN 35 fun s => Nat.land (Nat.shiftRight (BC s) 16) 65535) 1344)
  (CFSG.KLie.CT.andB (Nat.beq (sumN 35 fun s => Nat.land (Nat.shiftRight (BC s) 32) 65535) 336)
    (allN 35 fun s => Nat.beq (Nat.shiftRight (BC s) 48) 0)))

end CFSG.KC.Q47K

end
