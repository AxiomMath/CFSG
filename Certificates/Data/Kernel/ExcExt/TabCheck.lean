module

public import Certificates.Data.Kernel.ExcExt.Twin

public section

namespace CFSG.ExcExtK

@[expose] noncomputable def maskK (n : Nat) (p : Nat → Bool) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i acc => nif (p i) (Nat.lor acc (Nat.shiftLeft 1 i)) acc) n

@[expose] noncomputable def exI (d x i k : Nat) : Int := (ln4 x (Nat.add (Nat.mul d i) k) : Int) - 8

@[expose] noncomputable def decI (d r x : Nat) : List (List Int) :=
  (List.range r).map fun i => (List.range d).map fun k => exI d x i k

@[expose] noncomputable def resOK (n x x3 : Nat) : Bool :=
  allN n fun t => Nat.beq (ln2 x3 t) (Nat.mod (Nat.succ (ln4 x t)) 3)

@[expose] noncomputable def pairLaneOK (d fx hx pr8 i j : Nat) : Bool :=
  Nat.beq
    (Nat.add pr8 (Nat.mul 8 (Nat.add (sumN d fun k => ln4 fx (Nat.add (Nat.mul d i) k))
      (sumN d fun k => ln4 hx (Nat.add (Nat.mul d j) k)))))
    (Nat.add (sumN d fun k =>
      Nat.mul (ln4 fx (Nat.add (Nat.mul d i) k)) (ln4 hx (Nat.add (Nat.mul d j) k)))
      (Nat.add (Nat.mul 64 d) 8))

@[expose] noncomputable def pairOK (K : KT) (d fx hx : Nat) : Bool :=
  allN K.r fun i => allN K.r fun j => pairLaneOK d fx hx (prK K i j) i j

@[expose] noncomputable def adjOK (K : KT) : Bool :=
  band (Nat.blt K.adj (Nat.pow 2 (Nat.mul 128 K.r))) <|
  allN K.r fun i => Nat.beq (adjK K i)
    (maskK K.r fun j => bor (bnot (Nat.beq (prK K i j) 8)) (bnot (Nat.beq (prK K j i) 8)))

@[expose] noncomputable def zBitK (K : KT) (c t : Nat) : Bool :=
  Nat.beq (Nat.mod (sumN K.d fun k => Nat.mul (fK K t k) (digK c k)) 3) 0

@[expose] noncomputable def zmRangeOK (K : KT) (lo n : Nat) : Bool :=
  allN n fun i => Nat.beq (zmK K (Nat.add lo i)) (maskK K.r (zBitK K (Nat.add lo i)))

@[expose] noncomputable def zmBoundOK (K : KT) : Bool :=
  Nat.blt K.zm (Nat.pow 2 (Nat.mul 128 (Nat.pow 3 K.d)))

@[expose] noncomputable def eq3 (a b : Nat) : Bool := Nat.beq (Nat.mod (Nat.add a (Nat.mul 2 b)) 3) 0

@[expose] noncomputable def rtEqK (K : KT) (t' u t : Nat) (pos : Bool) : Bool :=
  allN K.d fun k =>
    let vf := Nat.add (fK K t k) (Nat.mul 2 (Nat.mul (Nat.succ (prK K t u)) (fK K u k)))
    let vh := Nat.add (hK K t k) (Nat.mul 2 (Nat.mul (Nat.succ (prK K u t)) (hK K u k)))
    band (Bool.rec (motive := fun _ => Bool) (Nat.beq (Nat.mod (Nat.add (fK K t' k) vf) 3) 0)
        (eq3 (fK K t' k) vf) pos)
      (Bool.rec (motive := fun _ => Bool) (Nat.beq (Nat.mod (Nat.add (hK K t' k) vh) 3) 0)
        (eq3 (hK K t' k) vh) pos)

@[expose] noncomputable def lgOK (K : KT) (L : List Bool) : Bool :=
  allN K.r fun t => Bool.rec (motive := fun _ => Bool) (bnot (L.getD t false)) (L.getD t false) (bit K.lg t)

@[expose] noncomputable def rtOK (K : KT) : Bool :=
  allN K.r fun u => allN K.r fun t =>
    band (Nat.blt (rtK K u t) K.r) (bor (rtEqK K (rtK K u t) u t true) (rtEqK K (rtK K u t) u t false))

@[expose] noncomputable def tabBool (m d r : Nat) (K : KT) (F H F' H' : List (List Int)) (d' : Nat)
    (fx hx fx' hx' : Nat) (L : List Bool) : Bool :=
  band (Nat.beq K.m m) <| band (Nat.beq K.d d) <| band (Nat.beq K.r r) <|
  band (F == decI d r fx) <| band (H == decI d r hx) <|
  band (F' == decI d' r fx') <| band (H' == decI d' r hx') <|
  band (resOK (Nat.mul d r) fx K.f3) <| band (resOK (Nat.mul d r) hx K.h3) <|
  band (pairOK K d' fx' hx') <| band (adjOK K) <| band (zmBoundOK K) <|
  band (rtOK K) (lgOK K L)

end CFSG.ExcExtK

end
