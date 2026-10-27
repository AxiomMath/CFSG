module

public import Certificates.Data.Kernel.ExcExt.CensusTwin

public section

namespace CFSG.ExcExtK

inductive KRefI where
  | none
  | zero
  | disc (S : Nat)
  | cent (w : Nat)
  | label
  | q2
  | outs (φ : Nat)

structure KILine where
  cv : Nat
  ref : KRefI
  planes : List KCPlane

@[expose] noncomputable def refLIK (T : KT) (cv : Nat) (e : KRefI) : Bool :=
  KRefI.rec (motive := fun _ => Bool) false
    (Nat.beq cv 0)
    (fun S => discK T (zmK T cv) S)
    (fun w => band (Nat.blt w (Nat.pow 3 T.d)) <|
      band (subK (truncK T.r (zmK T cv)) (zmK T w)) (offPlaneK T.d cv 0 w))
    (bnot (lam2K (labK T (zmK T cv))))
    (bnot (q2K (labK T (zmK T cv))))
    (fun φ => outK T (zmK T cv) φ cv)
    e

@[expose] noncomputable def ibodyK (T : KT) (cv cy : Nat) (X : KCW) : Bool :=
  KCW.rec (motive := fun _ => Bool) false (fun _ _ _ _ _ _ => false)
    (fun a b rows B n w Ll Lk Bl Bk =>
      band (abK a b) <| band (candK T cv (combK T.d cv cy a b) rows B n) <|
      commonK T cv (combK T.d cv cy a b) (zmK T cv) (zmK T (combK T.d cv cy a b)) w Ll Lk Bl Bk)
    (fun _ => false) X

@[expose] noncomputable def iplaneK (T : KT) (cv : Nat) (P : KCPlane) : Bool :=
  bor (refPK T cv P.cy P.ref) (ibodyK T cv P.cy P.body)

@[expose] noncomputable def iwalkK (T : KT) (cv : Nat) (n : Nat) : List KCPlane → Bool :=
  Nat.rec (motive := fun _ => List KCPlane → Bool)
    (fun ps => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) ps)
    (fun i ih ps => Bool.rec (motive := fun _ => Bool) (ih ps)
      (List.rec (motive := fun _ => Bool) false
        (fun P tl _ => band (Nat.beq P.cy i) (band (iplaneK T cv P) (ih tl))) ps)
      (canonK T.d cv i)) n

@[expose] noncomputable def scanLineIK (T : KT) (L : KILine) : Bool :=
  bor (refLIK T L.cv L.ref) (iwalkK T L.cv (Nat.pow 3 T.d) L.planes)

inductive KNbr where
  | small (g : Nat) (L : KL)
  | weyl (w : KLin) (L : KL)

structure KComp where
  k : Nat
  n : Nat
  W : KNbr

@[expose] noncomputable def nbrWK (T : KT) (k : Nat) (W : KNbr) : Bool :=
  KNbr.rec (motive := fun _ => Bool)
    (fun g L => band (Nat.ble (cardK T.r g) 2) (genK T g k L))
    (fun w L => band (linK T w) <| band (genK T (nodeMaskK w fun _ => true) k L) (notB2K T k))
    W

@[expose] noncomputable def compsK (T : KT) (z : Nat) : List KComp → Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun C _ ih => band (connK T C.k C.n) <| band (subK (truncK T.r C.k) z) <|
      band (allN T.r fun i => bor (bnot (bit C.k i)) (subK (Nat.land (adjK T i) z) C.k)) <|
      band (nbrWK T C.k C.W) ih)

@[expose] noncomputable def coverK (t : Nat) : List KComp → Bool :=
  List.rec (motive := fun _ => Bool) false (fun C _ ih => bor (bit C.k t) ih)

@[expose] noncomputable def nbrLineK (T : KT) (cv : Nat) (cs : List KComp) : Bool :=
  band (compsK T (zmK T cv) cs) <|
    allN T.r fun t => bor (bnot (bit (zmK T cv) t)) (coverK t cs)

end CFSG.ExcExtK

end
