module

public import Certificates.Data.Kernel.ExcExt.InLNbrTwin

public section

namespace CFSG.ExcExtK

@[expose] noncomputable def unsignedK (w : KLin) : Bool :=
  allN w.nodes.len fun i => bnot (bit w.neg i)

@[expose] noncomputable def selE6K (T : KT) (k : Nat) (w : KLin) (L : KL) : Bool :=
  band (Nat.beq w.tc 4) <| band (unsignedK w) <| band (typeK T w) <|
  band (genK T (nodeMaskK w fun _ => true) k L) (notB2K T k)

@[expose] noncomputable def selD6K (T : KT) (j k : Nat) (w : KLin) (L L' : KL) : Bool :=
  band (Nat.beq w.tc 3) <| band (Nat.beq w.n 6) <|
  band (bor (Nat.beq w.b 4) (Nat.beq w.b 5)) <| band (typeK T w) <|
  band (genK T (nodeMaskK w fun _ => true) k L) <|
  band (genK T (nodeMaskK w fun i => bnot (Nat.beq i w.b)) j L') <|
  band (notB2K T j) (notB2K T k)

structure KE6 where
  k : Nat
  w : KLin
  L : KL

@[expose] noncomputable def reflMaskK (T : KT) (u n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun t acc => nif (bit n t) (Nat.lor acc (Nat.shiftLeft 1 (rtK T u t))) acc) T.r

@[expose] noncomputable def memE6K (k : Nat) (Es : List KE6) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun E _ ih => bor (Nat.beq E.k k) ih) Es

@[expose] noncomputable def e6OKK (T : KT) (Es : List KE6) (E : KE6) : Bool :=
  band (selE6K T E.k E.w E.L) <| allN T.r fun u => memE6K (reflMaskK T u E.k) Es

@[expose] noncomputable def e6AllK (T : KT) (Es : List KE6) : List KE6 → Bool :=
  List.rec (motive := fun _ => Bool) true (fun E _ ih => band (e6OKK T Es E) ih)

inductive KLW where
  | ref
  | leaf (w : KLin) (Ll Lk : KL) (Bl Bk : Nat)
  | d6 (w : KLin) (L L' : KL)
  | e6

structure KLPlane where
  cy : Nat
  ref : KRefP
  wits : List KLW

structure KLLine where
  cv : Nat
  ref : KRefI
  planes : List KLPlane
  cref : Nat

@[expose] noncomputable def lwK (T : KT) (Es : List KE6) (cv cy cz : Nat) (X : KLW) : Bool :=
  KLW.rec (motive := fun _ => Bool) false
    (fun w Ll Lk Bl Bk =>
      band (commonK T cv cz (zmK T cv) (zmK T cz) w Ll Lk Bl Bk) (leafK w.tc w.n w.b))
    (fun w L L' => selD6K T (Nat.land (zmK T cv) (zmK T cy)) (zmK T cz) w L L')
    (memE6K (zmK T cz) Es) X

@[expose] noncomputable def lcandsK (T : KT) (Es : List KE6) (cv cy cref : Nat) :
    List KLW → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i 6)
    (fun X _ ih i =>
      let cz := combK T.d cv cy (Nat.div i 2) (Nat.succ (Nat.mod i 2))
      band (bor (refCK T cv cz (ln128 cref cz)) (lwK T Es cv cy cz X)) (ih (Nat.succ i)))

@[expose] noncomputable def lplaneK (T : KT) (Es : List KE6) (cv cref : Nat) (P : KLPlane) :
    Bool :=
  bor (refPK T cv P.cy P.ref) (lcandsK T Es cv P.cy cref P.wits 0)

@[expose] noncomputable def lwalkK (T : KT) (Es : List KE6) (cv cref : Nat) (n : Nat) :
    List KLPlane → Bool :=
  Nat.rec (motive := fun _ => List KLPlane → Bool)
    (fun ps => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) ps)
    (fun i ih ps => Bool.rec (motive := fun _ => Bool) (ih ps)
      (List.rec (motive := fun _ => Bool) false
        (fun P tl _ => band (Nat.beq P.cy i) (band (lplaneK T Es cv cref P) (ih tl))) ps)
      (canonK T.d cv i)) n

@[expose] noncomputable def scanLineLK (T : KT) (Es : List KE6) (L : KLLine) : Bool :=
  bor (refLIK T L.cv L.ref) (lwalkK T Es L.cv L.cref (Nat.pow 3 T.d) L.planes)

@[expose] noncomputable def pairRangeK (T : KT) : Bool :=
  allN T.r fun i => allN T.r fun j =>
    Bool.rec (motive := fun _ => Bool)
      (band (Nat.ble 7 (prK T i j)) (Nat.ble (prK T i j) 9)) (Nat.beq (prK T i j) 10) (Nat.beq i j)

end CFSG.ExcExtK

end
