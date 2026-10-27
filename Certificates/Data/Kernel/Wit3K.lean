module

public import Certificates.Data.Kernel.Misc.ArrEnum
public import Certificates.Data.Kernel.Spor.Prim

public section

namespace CFSG.KC.Wit3

open CFSG.KC.Enum (pg pcomp pidn strictB)
open CFSG.KS (mask pinvS)
open CFSG.KC.Misc.ArrEnum (permB keyK)

@[expose] noncomputable def decI (c : Nat) : Int :=
  Bool.rec (Int.negSucc (Nat.div c (nat_lit 2))) (Int.ofNat (Nat.succ (Nat.div c (nat_lit 2))))
    (Nat.beq (Nat.mod c (nat_lit 2)) (nat_lit 0))

@[expose] noncomputable def getL (L : List (List Nat)) (i : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun x _ ih i => Nat.rec (motive := fun _ => List Nat) x (fun j _ => ih j) i) L i

@[expose] noncomputable def getW (L : List (List Nat)) (i : Nat) : List Int := (getL L i).map decI

structure Cert where
  ng : Nat
  G : Nat → Nat
  ws : List (List Nat)
  N : Nat
  PT : Nat → Nat
  EP : Nat → Nat
  PAR : Nat → Nat
  LAB : Nat → Nat
  ps : List Nat
  K : Nat → Nat
  SO : Nat → Nat
  SI : Nat → Nat

@[expose] noncomputable def EF (EP : Nat → Nat) (i k : Nat) : Nat := pg 12 (mask 12) (EP i) k

@[expose] noncomputable def keyOK (n w : Nat) (ps : List Nat) (PT K : Nat → Nat) (i : Nat) : Bool :=
  Nat.beq (K i) (keyK n w ps (PT i))

@[expose] noncomputable def ordOK (N : Nat) (K SO SI : Nat → Nat) (i : Nat) : Bool :=
  Nat.blt (SI i) N && Nat.beq (SO (SI i)) i &&
    (Nat.ble N (Nat.succ i) || Nat.blt (K (SO i)) (K (SO (Nat.succ i))))

@[expose] noncomputable def candK (NQ : Nat) (QT YS : Nat → Nat) (j : Nat) : Nat :=
  Bool.rec (YS (Nat.sub j NQ)) (QT j) (Nat.blt j NQ)

@[expose] noncomputable def witOneK (n w s y : Nat) : Bool :=
  permB n w y &&
    strictB (pcomp n w (mask w) y (pcomp n w (mask w) s (pinvS n w (mask w) y))) fun t =>
      Nat.beq (pcomp n w (mask w) t s) (pcomp n w (mask w) s t) && !Nat.beq t s &&
        !Nat.beq t (pinvS n w (mask w) s) && !Nat.beq t (pidn n w)

@[expose] noncomputable def witPtK (n w NQ ny : Nat) (PT QT YS W : Nat → Nat) (i : Nat) : Bool :=
  Nat.beq (PT i) (pidn n w) ||
    !Nat.beq (pcomp n w (mask w) (PT i) (pcomp n w (mask w) (PT i) (PT i))) (pidn n w) ||
    (Nat.blt (W i) (Nat.add NQ ny) && witOneK n w (PT i) (candK NQ QT YS (W i)))

end CFSG.KC.Wit3

end
