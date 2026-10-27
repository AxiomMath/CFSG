module

public import Certificates.Data.Kernel.ExcExt.Twin

public section

namespace CFSG.ExcExtK

@[expose] noncomputable def lowK (r c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) r
    (fun t acc => nif (Nat.blt acc r) acc (nif (bit c t) t r)) r

@[expose] noncomputable def growK (T : KT) (c S : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) S
    (fun t acc => nif (bit S t) (Nat.lor acc (Nat.land (adjK T t) c)) acc) T.r

@[expose] noncomputable def growNK (T : KT) (c S n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) S (fun _ acc => growK T c acc) n

@[expose] noncomputable def connK (T : KT) (c n : Nat) : Bool :=
  let c' := truncK T.r c
  band (Nat.blt (lowK T.r c') T.r) <| band (Nat.ble n T.r) <|
    Nat.beq (growNK T c' (Nat.shiftLeft 1 (lowK T.r c')) n) c'

@[expose] noncomputable def outK (T : KT) (c φ cv : Nat) : Bool :=
  band (allN T.r fun t => bor (bnot (bit c t))
      (Nat.beq (Nat.mod (sumN T.d fun k => Nat.mul (digK φ k) (hK T t k)) 3) 0)) <|
    bnot (Nat.beq (Nat.mod (sumN T.d fun k => Nat.mul (digK φ k) (digK cv k)) 3) 0)

@[expose] noncomputable def rowsW (rows : KL) : KLin := ⟨0, 0, rows, 0, 0, 0⟩

@[expose] noncomputable def candK (T : KT) (cv cz : Nat) (rows : KL) (B n : Nat) : Bool :=
  band (Nat.blt cz (Nat.pow 3 T.d)) <| band (connK T (zmK T cz) n) <|
  band (lineK T (rowsW rows) rows.len idK cz B) <| band (lam2K (labK T (zmK T cz))) <|
  band (bnot (subK (truncK T.r (zmK T cz)) (zmK T cv))) (notB2K T (zmK T cz))

@[expose] noncomputable def ambientK (T : KT) (cv cz l k : Nat) (w : KLin) (Lk La : KL)
    (Bk Bb B B' : Nat) : Bool :=
  band (ambK T cz cv k l w Lk La Bk Bb) <| band (invCK w.tc w.n (rkW w) idK B) <|
    invCK w.tc w.n (Nat.sub (rkW w) 1) (offK w.a) B'

inductive KCA where
  | ref
  | two
  | amb (w : KLin) (Lk La : KL) (Bk Bb B B' : Nat)

inductive KCW where
  | twoL
  | twoNode (a b : Nat) (rows : KL) (B φ n : Nat)
  | common (a b : Nat) (rows : KL) (B n : Nat) (w : KLin) (Ll Lk : KL) (Bl Bk : Nat)
  | cands (ws : List KCA)

structure KCPlane where
  cy : Nat
  ref : KRefP
  body : KCW

structure KCLine where
  cv : Nat
  ref : KRefL
  planes : List KCPlane
  cref : Nat

@[expose] noncomputable def refLCK (T : KT) (cv : Nat) (e : KRefL) : Bool :=
  KRefL.rec (motive := fun _ => Bool) false
    (Nat.beq cv 0)
    (fun S => discK T (zmK T cv) S)
    (fun w => band (Nat.blt w (Nat.pow 3 T.d)) <|
      band (subK (truncK T.r (zmK T cv)) (zmK T w)) (offPlaneK T.d cv 0 w))
    (bnot (lam2K (labK T (zmK T cv))))
    false
    (fun coef => inK T (zmK T cv) coef cv)
    e

@[expose] noncomputable def caK (T : KT) (cv cy cz : Nat) (X : KCA) : Bool :=
  KCA.rec (motive := fun _ => Bool) false
    (twoNodeK (labK T (zmK T cz)) (labK T (Nat.land (zmK T cv) (zmK T cy))))
    (fun w Lk La Bk Bb B B' => ambientK T cv cz (zmK T cv) (zmK T cz) w Lk La Bk Bb B B')
    X

@[expose] noncomputable def ccandsK (T : KT) (cv cy cref : Nat) : List KCA → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i 6)
    (fun X _ ih i =>
      let cz := combK T.d cv cy (Nat.div i 2) (Nat.succ (Nat.mod i 2))
      band (bor (refCK T cv cz (ln128 cref cz)) (caK T cv cy cz X)) (ih (Nat.succ i)))

@[expose] noncomputable def abK (a b : Nat) : Bool :=
  band (Nat.blt a 3) (bor (Nat.beq b 1) (Nat.beq b 2))

@[expose] noncomputable def cbodyK (T : KT) (cv cy cref : Nat) (X : KCW) : Bool :=
  KCW.rec (motive := fun _ => Bool)
    (twoNodeK (labK T (zmK T cv)) (labK T (Nat.land (zmK T cv) (zmK T cy))))
    (fun a b rows B φ n =>
      band (abK a b) <| band (candK T cv (combK T.d cv cy a b) rows B n) <|
      band (outK T (zmK T (combK T.d cv cy a b)) φ (combK T.d cv cy a b)) <|
      twoNodeK (labK T (zmK T (combK T.d cv cy a b))) (labK T (Nat.land (zmK T cv) (zmK T cy))))
    (fun a b rows B n w Ll Lk Bl Bk =>
      band (abK a b) <| band (candK T cv (combK T.d cv cy a b) rows B n) <|
      commonK T cv (combK T.d cv cy a b) (zmK T cv) (zmK T (combK T.d cv cy a b)) w Ll Lk Bl Bk)
    (fun ws => ccandsK T cv cy cref ws 0)
    X

@[expose] noncomputable def notCandsK (X : KCW) : Bool :=
  KCW.rec (motive := fun _ => Bool) true (fun _ _ _ _ _ _ => true)
    (fun _ _ _ _ _ _ _ _ _ _ => true) (fun _ => false) X

@[expose] noncomputable def cplaneK (T : KT) (cv cref : Nat) (P : KCPlane) : Bool :=
  bor (band (notCandsK P.body) (refPK T cv P.cy P.ref)) (cbodyK T cv P.cy cref P.body)

@[expose] noncomputable def cwalkK (T : KT) (cv cref : Nat) (n : Nat) : List KCPlane → Bool :=
  Nat.rec (motive := fun _ => List KCPlane → Bool)
    (fun ps => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) ps)
    (fun i ih ps => Bool.rec (motive := fun _ => Bool) (ih ps)
      (List.rec (motive := fun _ => Bool) false
        (fun P tl _ => band (Nat.beq P.cy i) (band (cplaneK T cv cref P) (ih tl))) ps)
      (canonK T.d cv i)) n

@[expose] noncomputable def scanLineCK (T : KT) (L : KCLine) : Bool :=
  bor (refLCK T L.cv L.ref) (cwalkK T L.cv L.cref (Nat.pow 3 T.d) L.planes)

end CFSG.ExcExtK

end
