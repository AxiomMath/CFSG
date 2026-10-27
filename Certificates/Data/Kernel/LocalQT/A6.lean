module

public import Certificates.Data.Kernel.Spor.Prim
public import Certificates.Data.Kernel.LocalQT.Lat

public section

namespace CFSG.KC.LQT.A6

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.Ord CFSG.KC.LQT.L

@[expose] noncomputable def getW (l : List (List Nat)) (i : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun x _ ih j => Bool.rec (motive := fun _ => List Nat) (ih (Nat.sub j 1)) x (Nat.beq j 0)) l i

@[expose] noncomputable def imgA (P0 P1 Q1 l p : Nat) : Nat :=
  pg 12 4095 (nIf(Nat.beq l 0, P0, nIf(Nat.beq l 1, P1, Q1))) p

@[expose] noncomputable def evWK (P0 P1 Q1 : Nat) (w : List Nat) (p : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) p (fun l _ ih => strictN ih (imgA P0 P1 Q1 l)) w

@[expose] noncomputable def evNodeK (P0 P1 Q1 : Nat) (y1 y2 par lab : List Nat) :
    Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ p => p)
    (fun _ ih k p => nIf(Nat.beq k 0, p,
      strictN (evWK P0 P1 Q1 (Bool.rec (motive := fun _ => List Nat) y2 y1
        (Nat.beq (S.getK lab k) 0)) p) (ih (S.getK par k))))

@[expose] noncomputable def powK (f : Nat → Nat) (e p : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) p (fun _ ih => strictN ih f) e

@[expose] noncomputable def fixK (f : Nat → Nat) : Bool :=
  allN 4 fun b => Nat.beq (f b) b

@[expose] noncomputable def ordPK (f : Nat → Nat) (m : Nat) : Bool :=
  andB (fixK (powK f m)) (notB (fixK f))

@[expose] noncomputable def eqB (f g : Nat → Nat) : Bool :=
  allN 4 fun b => Nat.beq (f b) (g b)

@[expose] noncomputable def keyB (f : Nat → Nat) : Nat :=
  Nat.add (f 0) (Nat.mul 3850 (Nat.add (f 1) (Nat.mul 3850 (Nat.add (f 2) (Nat.mul 3850 (f 3))))))

@[expose] noncomputable def distinctK (key : Nat → Nat) : Nat → NT → Bool :=
  Nat.rec (motive := fun _ => NT → Bool) (fun _ => true)
    (fun k ih t => strictB (key k) fun x =>
      bIf(memT t x, false, ih (insT t x)))

@[expose] noncomputable def a6K (P0 P1 Q1 : Nat) (y1 y2 c par lab : List Nat)
    (cw : List (List Nat)) : Bool :=
  S.allBs [canonK 3850 12 4095 46200 P0, canonK 3850 12 4095 46200 P1,
    canonK 3850 12 4095 46200 Q1,
    ordPK (evWK P0 P1 Q1 y1) 3, ordPK (evWK P0 P1 Q1 y2) 5,
    eqB (fun p => evWK P0 P1 Q1 y1 (evWK P0 P1 Q1 c p))
      (fun p => evWK P0 P1 Q1 c (evWK P0 P1 Q1 y1 p)),
    eqB (fun p => evWK P0 P1 Q1 y2 (evWK P0 P1 Q1 c p))
      (fun p => evWK P0 P1 Q1 c (evWK P0 P1 Q1 y2 p)),
    Nat.beq (lenA par) 360, Nat.beq (lenA lab) 360,
    distinctK (fun k => keyB (evNodeK P0 P1 Q1 y1 y2 par lab 360 k)) 360 NT.lf,
    allN 360 fun k => P.impB (ordPK (evNodeK P0 P1 Q1 y1 y2 par lab 360 k) 2)
      (eqB (fun p => evWK P0 P1 Q1 (getW cw k) (evWK P0 P1 Q1 c p))
        (fun p => evWK P0 P1 Q1 c (evNodeK P0 P1 Q1 y1 y2 par lab 360 k
          (evWK P0 P1 Q1 (getW cw k) p))))]

end CFSG.KC.LQT.A6

end
