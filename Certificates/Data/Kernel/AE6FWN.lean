module

public import Certificates.Data.Kernel.AE6FN

public section

namespace CFSG.KC.AE6FW

open CFSG.KC.Enum CFSG.KS CFSG.KC.YoshQ CFSG.KC.AE6F

@[expose] noncomputable def commAt (m x y : Nat) : Bool :=
  strictB (x % 2 ^ (360 * 9)) fun x => strictB (y % 2 ^ (360 * 9)) fun y =>
    allN m fun i => Nat.beq (pg 9 (mask 9) x (pg 9 (mask 9) y i)) (pg 9 (mask 9) y (pg 9 (mask 9) x i))

@[expose] noncomputable def commF (x y : Nat) : Bool := commAt 8 x y && commN x y

@[expose] noncomputable def sqOneN (x : Nat) : Bool := eqN 360 9 (pmN 360 9 x x) (pidn 360 9)

@[expose] noncomputable def q8SpanN (i j : Nat) : List Nat :=
  [pidn 360 9, pmN 360 9 i i, i, invN 360 9 i, j, invN 360 9 j, pmN 360 9 i j, pmN 360 9 j i]

@[expose] noncomputable def twinPairsN (G : List Nat) (C : List (List Nat)) : List (Nat × Nat) :=
  C.map fun c =>
    (pmN 360 9 (pmN 360 9 (awN G c) (awN G (Certificates.AE6Model.kWords.getD 0 [])))
        (invN 360 9 (awN G c)),
      pmN 360 9 (pmN 360 9 (awN G c) (awN G (Certificates.AE6Model.kWords.getD 1 [])))
        (invN 360 9 (awN G c)))

@[expose] noncomputable def fwCommN (WL : List Nat) : Bool :=
  WL.all fun X => WL.all fun Y => commF X Y

@[expose] noncomputable def fwInSN (SL WL : List Nat) : Bool := WL.all (memN SL)

@[expose] noncomputable def fwNormN (TP : List (Nat × Nat)) (WL : List Nat) : Bool :=
  TP.all fun p => (q8SpanN p.1 p.2).all fun s =>
    WL.all fun T => memN WL (conjN s (invN 360 9 s) T)

@[expose] noncomputable def fwMeetN (TP : List (Nat × Nat)) (WL : List Nat) : Bool :=
  TP.all fun p => (q8SpanN p.1 p.2).any fun x =>
    memN WL x && !sqOneN x &&
      eqN 360 9 (pmN 360 9 (pmN 360 9 (pmN 360 9 x x) x) x) (pidn 360 9) &&
      (q8SpanN p.1 p.2).all fun s => !memN WL s ||
        memN [pidn 360 9, x, pmN 360 9 x x, pmN 360 9 (pmN 360 9 x x) x] s

@[expose] noncomputable def frameCandsN (TP : List (Nat × Nat)) (k : Nat) : List Nat :=
  let p := TP.getD k (pidn 360 9, pidn 360 9)
  (q8SpanN p.1 p.2).filter fun X => !sqOneN X

@[expose] def framesG {α β : Type} (ST : List β) (K0 K1 K2 K3 : List α)
    (c0 c1 c2 c3 : β → α → Bool) (w0 w1 w2 w3 : α → Bool) : Bool :=
  K0.all fun X0 =>
    let C0 := ST.filter fun T => c0 T X0
    K1.all fun X1 =>
      let C1 := C0.filter fun T => c1 T X1
      K2.all fun X2 =>
        let C2 := C1.filter fun T => c2 T X2
        K3.all fun X3 =>
          let C3 := C2.filter fun T => c3 T X3
          decide (C3.length < 64) || (C3.length == 64 && (w0 X0 && w1 X1 && w2 X2 && w3 X3))

@[expose] def bitsOf (L : List Bool) : Nat := L.foldr Nat.bit 0

@[expose] def fwFramesI (SIG : List Nat) (WB n0 n1 n2 n3 : Nat) : Bool :=
  framesG SIG (List.range' 0 n0) (List.range' n0 n1) (List.range' (n0 + n1) n2)
    (List.range' (n0 + n1 + n2) n3) Nat.testBit Nat.testBit Nat.testBit Nat.testBit
    WB.testBit WB.testBit WB.testBit WB.testBit

end CFSG.KC.AE6FW

end
