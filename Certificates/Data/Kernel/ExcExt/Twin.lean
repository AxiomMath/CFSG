module

public section

namespace CFSG.ExcExtK

@[expose] noncomputable def band (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) false b a

@[expose] noncomputable def bor (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) b true a

@[expose] noncomputable def bnot (a : Bool) : Bool := Bool.rec (motive := fun _ => Bool) true false a

@[expose] noncomputable def allN (n : Nat) (p : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => band (p i) ih) n

@[expose] noncomputable def anyN (n : Nat) (p : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun i ih => bor (p i) ih) n

@[expose] noncomputable def sumN (n : Nat) (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i acc => Nat.add acc (f i)) n

@[expose] noncomputable def nif (b : Bool) (x y : Nat) : Nat := Bool.rec (motive := fun _ => Nat) y x b

@[expose] noncomputable def ln2 (x i : Nat) : Nat := Nat.land (Nat.shiftRight x (Nat.mul 2 i)) 3

@[expose] noncomputable def ln4 (x i : Nat) : Nat := Nat.land (Nat.shiftRight x (Nat.mul 4 i)) 15

@[expose] noncomputable def ln7 (x i : Nat) : Nat := Nat.land (Nat.shiftRight x (Nat.mul 7 i)) 127

@[expose] noncomputable def ln9 (x i : Nat) : Nat := Nat.land (Nat.shiftRight x (Nat.mul 9 i)) 511

@[expose] noncomputable def ln14 (x i : Nat) : Nat := Nat.land (Nat.shiftRight x (Nat.mul 14 i)) 16383

@[expose] noncomputable def ln128 (x i : Nat) : Nat :=
  Nat.land (Nat.shiftRight x (Nat.mul 128 i)) 340282366920938463463374607431768211455

@[expose] noncomputable def bit (x i : Nat) : Bool := Nat.blt 0 (Nat.land x (Nat.shiftLeft 1 i))

@[expose] noncomputable def digK (c k : Nat) : Nat := Nat.mod (Nat.div c (Nat.pow 3 k)) 3

@[expose] noncomputable def truncK (r c : Nat) : Nat := Nat.land c (Nat.sub (Nat.pow 2 r) 1)

@[expose] noncomputable def subK (c c' : Nat) : Bool := Nat.beq (Nat.land c c') c

@[expose] noncomputable def cardK (r c : Nat) : Nat :=
  sumN r fun t => Nat.land (Nat.shiftRight c t) 1

structure KT where
  m : Nat
  d : Nat
  r : Nat
  f3 : Nat
  h3 : Nat
  pr : Nat
  rt : Nat
  adj : Nat
  zm : Nat
  lg : Nat

structure KL where
  len : Nat
  P : Nat

structure KLin where
  tc : Nat
  n : Nat
  nodes : KL
  neg : Nat
  a : Nat
  b : Nat

inductive KWit where
  | twoL
  | twoK
  | leaf (w : KLin) (Ll Lk : KL) (Bl Bk : Nat)
  | inner (w : KLin) (L : KL) (B Bi : Nat)
  | det (w : KLin) (L : KL) (B x : Nat)
  | ambD (w : KLin) (Lk La : KL) (Bk Bb : Nat) (perm : KL) (h : Nat)
  | d5 (w : KLin) (Lk La : KL) (Bk Bb : Nat) (Lj : KL)

inductive KRefL where
  | none
  | zero
  | disc (S : Nat)
  | cent (w : Nat)
  | label
  | q2
  | ins (coef : KL)

inductive KRefP where
  | none
  | disc (S : Nat)
  | cent (w : Nat)
  | label

structure KPlane where
  cy : Nat
  ref : KRefP
  wits : List KWit

structure KLine where
  cv : Nat
  ref : KRefL
  planes : List KPlane
  cref : Nat

@[expose] noncomputable def fK (T : KT) (t k : Nat) : Nat := ln2 T.f3 (Nat.add (Nat.mul T.d t) k)

@[expose] noncomputable def hK (T : KT) (t k : Nat) : Nat := ln2 T.h3 (Nat.add (Nat.mul T.d t) k)

@[expose] noncomputable def prK (T : KT) (i j : Nat) : Nat := ln4 T.pr (Nat.add (Nat.mul T.r i) j)

@[expose] noncomputable def rtK (T : KT) (u t : Nat) : Nat := ln7 T.rt (Nat.add (Nat.mul T.r u) t)

@[expose] noncomputable def adjK (T : KT) (i : Nat) : Nat := ln128 T.adj i

@[expose] noncomputable def zmK (T : KT) (c : Nat) : Nat := ln128 T.zm c

@[expose] noncomputable def ofDigK (d : Nat) (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun k acc => Nat.add acc (Nat.mul (Nat.mod (f k) 3) (Nat.pow 3 k))) d

@[expose] noncomputable def combK (d cv cy a b : Nat) : Nat :=
  ofDigK d fun k => Nat.add (Nat.mul a (digK cv k)) (Nat.mul b (digK cy k))

@[expose] noncomputable def pivUp (c n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun k p => nif (Nat.blt p k) p (nif (bnot (Nat.beq (digK c k) 0)) k (Nat.succ k))) n

@[expose] noncomputable def pivK (d c : Nat) : Nat := pivUp c d

@[expose] noncomputable def canonK (d cv cy : Nat) : Bool :=
  band (Nat.blt cy (Nat.pow 3 d)) (band (Nat.beq (digK cy (pivK d cv)) 0)
    (band (Nat.blt (pivK d cy) d) (Nat.beq (digK cy (pivK d cy)) 1)))

@[expose] noncomputable def offPlaneK (d cv cy w : Nat) : Bool :=
  allN 3 fun a => allN 3 fun b => bnot (Nat.beq w (combK d cv cy a b))

@[expose] noncomputable def closedK (T : KT) (c S : Nat) : Bool :=
  let c' := truncK T.r c
  let S' := Nat.land S c'
  band (bnot (Nat.beq S' 0)) (band (bnot (Nat.beq S' c'))
    (allN T.r fun t => bor (bnot (bit S' t)) (subK (Nat.land (adjK T t) c') S')))

@[expose] noncomputable def discK (T : KT) (c S : Nat) : Bool :=
  bor (Nat.beq (truncK T.r c) 0) (closedK T c S)

@[expose] noncomputable def labC (t r n : Nat) : Nat := Nat.add t (Nat.add (Nat.mul 32 r) (Nat.mul 1024 n))

@[expose] noncomputable def labF4K (n : Nat) : Nat :=
  nif (Nat.beq n 1) (labC 0 1 1) <| nif (Nat.beq n 3) (labC 1 2 1) <|
  nif (Nat.beq n 4) (labC 15 0 1) <| nif (Nat.beq n 6) (labC 1 3 1) <|
  nif (Nat.beq n 9) (labC 3 3 1) <| nif (Nat.beq n 12) (labC 4 4 1) <|
  nif (Nat.beq n 16) (labC 3 4 1) <| nif (Nat.beq n 24) (labC 9 0 1) 0

@[expose] noncomputable def labE6K (n l : Nat) : Nat :=
  nif (band (Nat.beq n 1) (Nat.beq l 0)) (labC 0 1 2) <|
  nif (band (Nat.beq n 3) (Nat.beq l 0)) (labC 0 2 2) <|
  nif (band (Nat.beq n 1) (Nat.beq l 1)) (labC 0 1 1) <|
  nif (band (Nat.beq n 3) (Nat.beq l 3)) (labC 1 2 1) <|
  nif (band (Nat.beq n 6) (Nat.beq l 6)) (labC 1 3 1) <|
  nif (band (Nat.beq n 12) (Nat.beq l 12)) (labC 4 4 1) <|
  nif (band (Nat.beq n 4) (Nat.beq l 2)) (labC 0 3 1) <|
  nif (band (Nat.beq n 9) (Nat.beq l 3)) (labC 0 5 1) <|
  nif (band (Nat.beq n 9) (Nat.beq l 6)) (labC 5 4 1) <|
  nif (band (Nat.beq n 16) (Nat.beq l 12)) (labC 4 5 1) <|
  nif (band (Nat.beq n 24) (Nat.beq l 12)) (labC 6 0 1) 0

@[expose] noncomputable def labSLK (n o : Nat) : Nat :=
  nif (Nat.beq n 1) (labC 0 1 1) <| nif (Nat.beq n 3) (labC 1 2 1) <|
  nif (Nat.beq n 6) (labC 1 3 1) <| nif (Nat.beq n 10) (labC 1 4 1) <|
  nif (Nat.beq n 15) (labC 1 5 1) <| nif (Nat.beq n 21) (labC 1 6 1) <|
  nif (Nat.beq n 28) (labC 1 7 1) <|
  nif (Nat.beq n 36) (nif (Nat.beq o 756) (labC 1 8 1) (labC 10 0 1)) <|
  nif (Nat.beq n 12) (labC 4 4 1) <| nif (Nat.beq n 20) (labC 5 5 1) <|
  nif (Nat.beq n 30) (labC 4 6 1) <| nif (Nat.beq n 42) (labC 5 7 1) <|
  nif (Nat.beq n 56) (labC 4 8 1) <| nif (Nat.beq n 63) (labC 7 0 1) <|
  nif (Nat.beq n 120) (labC 8 0 1) 0

@[expose] noncomputable def orthK (T : KT) (c : Nat) : Nat :=
  sumN T.r fun i => nif (bit c i)
    (sumN T.r fun j => nif (band (bit c j) (Nat.beq (prK T i j) 8)) 1 0) 0

@[expose] noncomputable def labK (T : KT) (c : Nat) : Nat :=
  nif (Nat.beq T.m 0) (labF4K (cardK T.r c)) <|
  nif (Nat.beq T.m 1) (labE6K (cardK T.r c) (cardK T.r (Nat.land c T.lg))) <|
  labSLK (cardK T.r c) (orthK T c)

@[expose] noncomputable def labT (x : Nat) : Nat := Nat.mod x 32

@[expose] noncomputable def labR (x : Nat) : Nat := Nat.mod (Nat.div x 32) 32

@[expose] noncomputable def labN (x : Nat) : Nat := Nat.div x 1024

@[expose] noncomputable def lam2P (t r n : Nat) : Bool :=
  band (Nat.ble 1 n) <|
  Bool.rec (motive := fun _ => Bool)
  (Bool.rec (motive := fun _ => Bool)
  (Bool.rec (motive := fun _ => Bool)
  (Bool.rec (motive := fun _ => Bool)
  (Bool.rec (motive := fun _ => Bool)
  (Bool.rec (motive := fun _ => Bool)
  (Bool.rec (motive := fun _ => Bool)
  (Bool.rec (motive := fun _ => Bool) false
    (band (Nat.beq r 0) (Nat.beq n 1)) (band (Nat.ble 15 t) (Nat.ble t 17)))
    (band (Nat.beq r 0) (band (Nat.beq (Nat.mod n 2) 1) (Nat.ble 3 n)))
    (band (Nat.ble 13 t) (Nat.ble t 14)))
    (band (Nat.beq r 0) (Nat.ble 2 n)) (Nat.beq t 12))
    (Nat.beq r 0) (band (Nat.ble 6 t) (Nat.ble t 11)))
    (Nat.ble 2 r) (Nat.beq t 5))
    (Nat.ble 3 r) (Nat.beq t 4))
    (band (Nat.ble 2 r) (bor (bnot (Nat.beq r 2)) (Nat.ble 2 n))) (band (Nat.ble 1 t) (Nat.ble t 3)))
    (band (Nat.ble 1 r) (bor (bnot (Nat.beq r 1)) (Nat.ble 2 n))) (Nat.beq t 0)

@[expose] noncomputable def lam2K (x : Nat) : Bool := lam2P (labT x) (labR x) (labN x)

@[expose] noncomputable def q2K (x : Nat) : Bool :=
  bor (Nat.blt (labN x) 2)
    (band (Nat.beq (labT x) 0) (band (Nat.beq (labR x) 1) (Nat.beq (labN x) 2)))

@[expose] noncomputable def twoNodeP (xt xr xn jt jr jn : Nat) : Bool :=
  bor (band (Nat.beq jt 0) (band (Nat.beq xt 0) (band (Nat.beq xr (Nat.add jr 2))
      (band (Nat.beq xn jn) (band (Nat.beq (Nat.mod (Nat.add jr 3) 3) 0)
        (Nat.beq (Nat.mod (Nat.sub (Nat.pow 2 jn) 1) 3) 0)))))) <|
  bor (band (Nat.beq jt 1) (band (Nat.beq xt 1) (band (Nat.beq xr (Nat.add jr 2))
      (band (Nat.beq xn jn) (band (Nat.beq (Nat.mod (Nat.add jr 3) 3) 0)
        (Nat.beq (Nat.mod (Nat.add (Nat.pow 2 jn) 1) 3) 0)))))) <|
  bor (band (Nat.beq jt 4) (band (Nat.beq jr 4) (band (Nat.beq xt 6) (band (Nat.beq xn jn)
      (Nat.beq (Nat.mod (Nat.sub (Nat.pow 2 jn) 1) 3) 0))))) <|
  band (Nat.beq jt 4) (band (Nat.beq jr 4) (band (Nat.beq xt 10) (band (Nat.beq xn jn)
      (Nat.beq (Nat.mod (Nat.add (Nat.pow 2 jn) 1) 3) 0))))

@[expose] noncomputable def twoNodeK (x j : Nat) : Bool :=
  twoNodeP (labT x) (labR x) (labN x) (labT j) (labR j) (labN j)

@[expose] noncomputable def notB2K (T : KT) (c : Nat) : Bool :=
  bnot (band (Nat.beq T.m 0) (Nat.beq (cardK T.r c) 4))

@[expose] noncomputable def rkK (tc n : Nat) : Nat :=
  nif (Nat.blt tc 4) n <| nif (Nat.beq tc 4) 6 <| nif (Nat.beq tc 5) 7 <|
  nif (Nat.beq tc 6) 8 <| nif (Nat.beq tc 7) 4 2

@[expose] noncomputable def validK (tc n : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
  (Bool.rec (motive := fun _ => Bool)
  (Bool.rec (motive := fun _ => Bool)
  (Bool.rec (motive := fun _ => Bool)
    (band (Nat.ble 4 tc) (Nat.ble tc 8))
    (Nat.ble 4 n) (Nat.beq tc 3))
    (Nat.ble 3 n) (Nat.beq tc 2))
    (Nat.ble 2 n) (Nat.beq tc 1))
    (Nat.ble 1 n) (Nat.beq tc 0)

@[expose] noncomputable def eqN (x y : Nat) : Bool := Nat.beq x y

@[expose] noncomputable def cartOff (tc n i j : Nat) : Nat :=
  nif (Nat.beq tc 0)
    (nif (bor (eqN (Nat.succ i) j) (eqN (Nat.succ j) i)) 7 8) <|
  nif (Nat.beq tc 1)
    (nif (eqN (Nat.succ i) j) (nif (eqN j (Nat.sub n 1)) 6 7) (nif (eqN (Nat.succ j) i) 7 8)) <|
  nif (Nat.beq tc 2)
    (nif (eqN (Nat.succ i) j) 7 (nif (eqN (Nat.succ j) i) (nif (eqN i (Nat.sub n 1)) 6 7) 8)) <|
  nif (Nat.beq tc 3)
    (nif (Nat.ble n 2) 8 <|
      nif (band (eqN (Nat.succ i) j) (Nat.blt (Nat.add j 2) n)) 7 <|
      nif (band (eqN (Nat.succ j) i) (Nat.blt (Nat.add i 2) n)) 7 <|
      nif (band (eqN (Nat.add i 3) n) (bor (eqN (Nat.add j 2) n) (eqN (Nat.succ j) n))) 7 <|
      nif (band (eqN (Nat.add j 3) n) (bor (eqN (Nat.add i 2) n) (eqN (Nat.succ i) n))) 7 8) <|
  nif (band (Nat.ble 4 tc) (Nat.ble tc 6))
    (nif (bor (band (eqN i 0) (eqN j 2)) <| bor (band (eqN j 0) (eqN i 2)) <|
        bor (band (eqN i 1) (eqN j 3)) <| bor (band (eqN j 1) (eqN i 3)) <|
        bor (band (Nat.ble 2 i) (eqN (Nat.succ i) j)) (band (Nat.ble 2 j) (eqN (Nat.succ j) i))) 7 8) <|
  nif (Nat.beq tc 7)
    (nif (bor (band (eqN i 0) (eqN j 1)) <| bor (band (eqN i 1) (eqN j 0)) <|
        bor (band (eqN i 2) (eqN j 1)) <| bor (band (eqN i 2) (eqN j 3)) (band (eqN i 3) (eqN j 2)))
      7 (nif (band (eqN i 1) (eqN j 2)) 6 8)) <|
  nif (band (eqN i 0) (eqN j 1)) 5 (nif (band (eqN i 1) (eqN j 0)) 7 8)

@[expose] noncomputable def cartK (tc n i j : Nat) : Nat := nif (Nat.beq i j) 10 (cartOff tc n i j)

@[expose] noncomputable def leafK (tc n a : Nat) : Bool :=
  Nat.beq (sumN (rkK tc n) fun c =>
    nif (band (bnot (Nat.beq c a)) (bnot (Nat.beq (cartK tc n a c) 8))) 1 0) 1

@[expose] noncomputable def innerK (tc n : Nat) : Bool :=
  bor (band (Nat.beq tc 1) (Nat.beq n 3)) <| bor (band (Nat.beq tc 2) (Nat.beq n 3)) <|
  bor (band (Nat.beq tc 3) (band (Nat.ble 5 n) (Nat.beq (Nat.mod n 2) 1))) <|
  bor (Nat.beq tc 4) (Nat.beq tc 5)

@[expose] noncomputable def nodeK (w : KLin) (i : Nat) : Nat :=
  nif (Nat.blt i w.nodes.len) (ln7 w.nodes.P i) 0

@[expose] noncomputable def negK (w : KLin) (i : Nat) : Bool := band (Nat.blt i w.nodes.len) (bit w.neg i)

@[expose] noncomputable def rkW (w : KLin) : Nat := rkK w.tc w.n

@[expose] noncomputable def typeK (T : KT) (w : KLin) : Bool :=
  band (validK w.tc w.n) <| band (Nat.beq w.nodes.len (rkW w)) <|
  band (allN w.nodes.len fun i => Nat.blt (nodeK w i) T.r) <|
  allN (rkW w) fun i => allN (rkW w) fun j =>
    Nat.beq
      (Bool.rec (motive := fun _ => Nat) (prK T (nodeK w i) (nodeK w j))
        (Nat.sub 16 (prK T (nodeK w i) (nodeK w j))) (bne (negK w i) (negK w j)))
      (cartK w.tc w.n i j)

@[expose] noncomputable def linK (T : KT) (w : KLin) : Bool :=
  band (typeK T w) <| band (Nat.ble (rkW w) 8) <| band (Nat.blt w.a (rkW w)) <|
  band (Nat.blt w.b (rkW w)) <|
  band (bnot (Nat.beq w.a w.b)) (leafK w.tc w.n w.a)

@[expose] noncomputable def nodeMaskK (w : KLin) (p : Nat → Bool) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => nif (p i) (Nat.lor acc (Nat.shiftLeft 1 (nodeK w i))) acc) (rkW w)

@[expose] noncomputable def offK (a p : Nat) : Nat := nif (Nat.blt p a) p (Nat.succ p)

@[expose] noncomputable def liveBit : Nat := 340282366920938463463374607431768211456

@[expose] noncomputable def derivK (T : KT) (gens : Nat) (L : KL) : Nat :=
  Nat.rec (motive := fun _ => Nat) (Nat.lor gens liveBit)
    (fun i S =>
      let e := ln14 L.P i
      let u := Nat.mod e 128
      let t := Nat.div e 128
      nif (band (Nat.blt u T.r) (band (Nat.blt t T.r) (band (bit gens u) (bit S t))))
        (Nat.lor S (Nat.shiftLeft 1 (rtK T u t))) 0) L.len

@[expose] noncomputable def genK (T : KT) (gens c : Nat) (L : KL) : Bool :=
  band (Nat.blt gens (Nat.pow 2 T.r)) <| band (subK gens c) <|
  (fun S => band (bnot (Nat.beq S 0)) (subK (truncK T.r c) S)) (derivK T gens L)

@[expose] noncomputable def joinK (T : KT) (l k t : Nat) (L : KL) : Bool :=
  band (Nat.blt t T.r) <|
  (fun S => band (bnot (Nat.beq S 0)) (bit S t)) (derivK T (Nat.lor (truncK T.r l) (truncK T.r k)) L)

@[expose] noncomputable def ndel (i j : Nat) : Nat := nif (Nat.beq i j) 2 0

@[expose] noncomputable def lineK (T : KT) (w : KLin) (cnt : Nat) (pos : Nat → Nat) (cz B : Nat) :
    Bool :=
  let p := pivK T.d cz
  band (Nat.blt cz (Nat.pow 3 T.d)) <| band (Nat.blt p T.d) <| band (Nat.beq (Nat.succ cnt) T.d) <|
  band (allN cnt fun i => band (Nat.blt (nodeK w (pos i)) T.r) (bit (zmK T cz) (nodeK w (pos i)))) <|
  allN T.d fun i => allN T.d fun j =>
    Nat.beq (Nat.mod (Nat.add (sumN T.d fun k =>
      Nat.mul (ln2 B (Nat.add (Nat.mul 8 i) k))
        (nif (Nat.blt (Nat.succ k) T.d) (fK T (nodeK w (pos k)) j) (nif (Nat.beq j p) 1 0)))
      (ndel i j)) 3) 0

@[expose] noncomputable def invCK (tc n k : Nat) (pos : Nat → Nat) (B : Nat) : Bool :=
  allN k fun i => allN k fun j =>
    Nat.beq (Nat.mod (Nat.add (sumN k fun l =>
      Nat.mul (ln2 B (Nat.add (Nat.mul 8 i) l)) (Nat.succ (cartK tc n (pos l) (pos j)))) (ndel i j)) 3) 0

@[expose] noncomputable def singK (tc n k x : Nat) : Bool :=
  band (anyN k fun l => bnot (Nat.beq (Nat.mod (ln2 x l) 3) 0)) <|
  allN k fun i => Nat.beq (Nat.mod (sumN k fun l =>
    Nat.mul (Nat.succ (cartK tc n i l)) (ln2 x l)) 3) 0

@[expose] noncomputable def indepK (T : KT) (w : KLin) (B : Nat) : Bool :=
  allN (rkW w) fun i => allN (rkW w) fun j =>
    Nat.beq (Nat.mod (Nat.add (sumN T.d fun l =>
      Nat.mul (hK T (nodeK w i) l) (ln2 B (Nat.add (Nat.mul 8 l) j))) (ndel i j)) 3) 0

@[expose] noncomputable def idK (p : Nat) : Nat := p

@[expose] noncomputable def nbrK (T : KT) (cz k : Nat) (w : KLin) (L : KL) (B : Nat) : Bool :=
  band (linK T w) <| band (genK T (nodeMaskK w fun _ => true) k L) <|
  band (lineK T w (rkW w) idK cz B) (notB2K T k)

@[expose] noncomputable def commonK (T : KT) (cv cz l k : Nat) (w : KLin) (Ll Lk : KL) (Bl Bk : Nat) :
    Bool :=
  band (linK T w) <|
  band (genK T (nodeMaskK w fun i => bnot (Nat.beq i w.a)) l Ll) <|
  band (genK T (nodeMaskK w fun i => bnot (Nat.beq i w.b)) k Lk) <|
  band (lineK T w (Nat.sub (rkW w) 1) (offK w.a) cv Bl) <|
  band (lineK T w (Nat.sub (rkW w) 1) (offK w.b) cz Bk) <|
  band (notB2K T l) (notB2K T k)

@[expose] noncomputable def ambK (T : KT) (cv cz l k : Nat) (w : KLin) (Lk La : KL) (Bk Bb : Nat) :
    Bool :=
  band (linK T w) <|
  band (genK T (nodeMaskK w fun i => bnot (Nat.beq i w.a)) k Lk) <|
  band (lineK T w (Nat.sub (rkW w) 1) (offK w.a) cz Bk) <|
  band (joinK T l k (nodeK w w.a) La) <|
  band (Nat.blt cv (Nat.pow 3 T.d)) <|
  band (allN (rkW w) fun i =>
    bor (bor (Nat.beq i w.a) (Nat.beq i w.b)) (bit (zmK T cv) (nodeK w i))) <|
  band (Nat.beq (rkW w) T.d) <| band (indepK T w Bb) <|
  band (notB2K T l) (notB2K T k)

@[expose] noncomputable def ambDK (T : KT) (cv cz l k : Nat) (w : KLin) (Lk La : KL) (Bk Bb : Nat)
    (perm : KL) (h : Nat) : Bool :=
  band (ambK T cv cz l k w Lk La Bk Bb) <| band (Nat.ble 3 h) <|
  band (Nat.beq (rkW w) (Nat.succ (Nat.mul 2 h))) <| band (Nat.beq perm.len (Nat.mul 2 h)) <|
  band (allN perm.len fun i => allN i fun j => bnot (Nat.beq (ln4 perm.P i) (ln4 perm.P j))) <|
  band (allN perm.len fun i =>
    band (Nat.blt (ln4 perm.P i) (rkW w)) (bnot (Nat.beq (ln4 perm.P i) w.a))) <|
  allN (Nat.mul 2 h) fun i => allN (Nat.mul 2 h) fun j =>
    Nat.beq (cartK w.tc w.n (ln4 perm.P i) (ln4 perm.P j)) (cartK 3 (Nat.mul 2 h) i j)

@[expose] noncomputable def d5K (T : KT) (cv cz l j k : Nat) (w : KLin) (Lk La : KL) (Bk Bb : Nat)
    (Lj : KL) : Bool :=
  band (ambK T cv cz l k w Lk La Bk Bb) <| band (Nat.beq w.tc 3) <| band (Nat.beq w.n 5) <|
  band (Nat.beq w.a 0) <|
  band (bor (Nat.beq w.b 1) (bor (Nat.beq w.b 3) (Nat.beq w.b 4))) <|
  band (genK T (nodeMaskK w fun i => band (bnot (Nat.beq i w.a)) (bnot (Nat.beq i w.b))) j Lj) <|
  band (notB2K T j) <|
  bor (Nat.beq (labK T j) (labC 1 3 1)) (Nat.beq (labK T j) (labC 5 3 1))

@[expose] noncomputable def witK (T : KT) (cv cy cz : Nat) (X : KWit) : Bool :=
  KWit.rec (motive := fun _ => Bool)
    (twoNodeK (labK T (zmK T cv)) (labK T (Nat.land (zmK T cv) (zmK T cy))))
    (twoNodeK (labK T (zmK T cz)) (labK T (Nat.land (zmK T cv) (zmK T cy))))
    (fun w Ll Lk Bl Bk =>
      band (commonK T cv cz (zmK T cv) (zmK T cz) w Ll Lk Bl Bk) (leafK w.tc w.n w.b))
    (fun w L B Bi =>
      band (nbrK T cz (zmK T cz) w L B) <|
      band (invCK w.tc w.n (rkW w) idK Bi) (innerK w.tc w.n))
    (fun w L B x =>
      band (nbrK T cz (zmK T cz) w L B) <|
      band (singK w.tc w.n (rkW w) x) (Nat.beq T.d (Nat.succ (rkW w))))
    (fun w Lk La Bk Bb perm h => ambDK T cv cz (zmK T cv) (zmK T cz) w Lk La Bk Bb perm h)
    (fun w Lk La Bk Bb Lj =>
      d5K T cv cz (zmK T cv) (Nat.land (zmK T cv) (zmK T cy)) (zmK T cz) w Lk La Bk Bb Lj)
    X

@[expose] noncomputable def inK (T : KT) (c : Nat) (coef : KL) (cv : Nat) : Bool :=
  band (allN coef.len fun i =>
    band (Nat.blt (Nat.mod (ln9 coef.P i) 128) T.r) (bit c (Nat.mod (ln9 coef.P i) 128))) <|
  allN T.d fun k =>
    Nat.beq (Nat.mod (Nat.add (sumN coef.len fun i =>
      Nat.mul (Nat.div (ln9 coef.P i) 128) (hK T (Nat.mod (ln9 coef.P i) 128) k)) (Nat.mul 2 (digK cv k))) 3) 0

@[expose] noncomputable def refLK (T : KT) (cv : Nat) (e : KRefL) : Bool :=
  KRefL.rec (motive := fun _ => Bool) false
    (Nat.beq cv 0)
    (fun S => discK T (zmK T cv) S)
    (fun w => band (Nat.blt w (Nat.pow 3 T.d)) <|
      band (subK (truncK T.r (zmK T cv)) (zmK T w)) (offPlaneK T.d cv 0 w))
    (bnot (lam2K (labK T (zmK T cv))))
    (bnot (q2K (labK T (zmK T cv))))
    (fun coef => inK T (zmK T cv) coef cv)
    e

@[expose] noncomputable def refPK (T : KT) (cv cy : Nat) (e : KRefP) : Bool :=
  KRefP.rec (motive := fun _ => Bool) false
    (fun S => discK T (Nat.land (zmK T cv) (zmK T cy)) S)
    (fun w => band (Nat.blt w (Nat.pow 3 T.d)) <|
      band (subK (truncK T.r (Nat.land (zmK T cv) (zmK T cy))) (zmK T w)) (offPlaneK T.d cv cy w))
    (bnot (lam2K (labK T (Nat.land (zmK T cv) (zmK T cy)))))
    e

@[expose] noncomputable def refCKAt (T : KT) (cv cz kd x : Nat) : Bool :=
    Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool) false
      (subK (truncK T.r (zmK T cz)) (zmK T cv)) (Nat.beq kd 4))
      (bnot (lam2K (labK T (zmK T cz)))) (Nat.beq kd 3))
      (band (Nat.blt x (Nat.pow 3 T.d)) <|
        band (subK (truncK T.r (zmK T cz)) (zmK T x)) (offPlaneK T.d cz 0 x)) (Nat.beq kd 2))
      (discK T (zmK T cz) x) (Nat.beq kd 1)

@[expose] noncomputable def refCK (T : KT) (cv cz e : Nat) : Bool :=
  refCKAt T cv cz (Nat.mod e 8) (Nat.div e 8)

@[expose] noncomputable def candsK (T : KT) (cv cy cref : Nat) (ws : List KWit) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i 6)
    (fun X _ ih i =>
      let cz := combK T.d cv cy (Nat.div i 2) (Nat.succ (Nat.mod i 2))
      band (bor (refCK T cv cz (ln128 cref cz)) (witK T cv cy cz X)) (ih (Nat.succ i))) ws

@[expose] noncomputable def planeK (T : KT) (cv cref : Nat) (P : KPlane) : Bool :=
  bor (refPK T cv P.cy P.ref) (candsK T cv P.cy cref P.wits 0)

@[expose] noncomputable def walkK (T : KT) (cv cref : Nat) (n : Nat) : List KPlane → Bool :=
  Nat.rec (motive := fun _ => List KPlane → Bool)
    (fun ps => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) ps)
    (fun i ih ps => Bool.rec (motive := fun _ => Bool) (ih ps)
      (List.rec (motive := fun _ => Bool) false
        (fun P tl _ => band (Nat.beq P.cy i) (band (planeK T cv cref P) (ih tl))) ps)
      (canonK T.d cv i)) n

@[expose] noncomputable def scanLineK (T : KT) (L : KLine) : Bool :=
  bor (refLK T L.cv L.ref) (walkK T L.cv L.cref (Nat.pow 3 T.d) L.planes)

end CFSG.ExcExtK

end
