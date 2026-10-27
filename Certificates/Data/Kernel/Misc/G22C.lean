module

public import Certificates.Data.Kernel.Misc.G22W

public section

namespace CFSG.KD.G22C

open CFSG.KD.G22W CFSG.KC.Mat8P CFSG.KC.Loop

@[expose] def isInvP (x : Nat) : Bool := Nat.beq (mulP x x) oneP && !(Nat.beq x oneP)

@[expose] def commN (x y : Nat) : Bool := Nat.beq (mulP x y) (mulP y x)

@[expose] noncomputable def cfld (C : Nat → Nat) (f t : Nat) : Nat :=
  Nat.land (Nat.shiftRight (C t) (Nat.mul 16 f)) 65535

@[expose] noncomputable def repT (R C : Nat → Nat) (n : Nat) (c : Bool) : Nat :=
  numX R (cond c (C (Nat.add n 1)) (C n))

@[expose] noncomputable def conjK (R C : Nat → Nat) (n hi : Nat) : Bool :=
  Nat.blt (C n) n && Nat.blt (C (Nat.add n 1)) n &&
    allBelow n hi fun t =>
      cond (isInvP (numX R t))
        (Nat.blt (cfld C 0 t) n && Nat.blt (cfld C 1 t) n &&
          Nat.beq (mulP (numX R (cfld C 0 t)) (numX R (cfld C 1 t))) oneP &&
          Nat.beq (mulP (numX R (cfld C 0 t)) (numX R t))
            (mulP (repT R C n (Nat.beq (cfld C 2 t) 1)) (numX R (cfld C 0 t))))
        true

@[expose] noncomputable def lstOf (C : Nat → Nat) (o k : Nat) : List Nat :=
  (List.range k).map fun i => C (Nat.add o i)

@[expose] noncomputable def invN (R : Nat → Nat) (n : Nat) : List Nat :=
  ((List.range n).map (numX R)).filter isInvP

@[expose] def eqL : List Nat → List Nat → Bool
  | [], [] => true
  | x :: l, y :: l' => Nat.beq x y && eqL l l'
  | _, _ => false

@[expose] noncomputable def clsL (C : Nat → Nat) (n : Nat) (c : Bool) : List Nat :=
  lstOf C (cond c (Nat.add (Nat.add n 4) (C (Nat.add n 2))) (Nat.add n 4))
    (C (Nat.add n (cond c 3 2)))

@[expose] noncomputable def classK (R C : Nat → Nat) (n : Nat) (c : Bool) : Bool :=
  eqL ((invN R n).filter (commN (repT R C n c))) (clsL C n c)

@[expose] def rankB {α : Type} (q : α → α → Bool) (m : α → α → α) (L : List α) (a : α) : Bool :=
  let Ca := L.filter fun b => q (m a b) (m b a)
  Ca.all fun b =>
    q b a ||
      let ab := m a b
      let Cab := Ca.filter fun c => q (m b c) (m c b)
      Cab.all fun c =>
        q c a || q c b || q c ab ||
          (Cab.filter fun e => q (m c e) (m e c)).all fun e =>
            q e a || q e b || q e c || q e ab || q e (m a c) || q e (m b c) || q e (m ab c)

@[expose] noncomputable def rankK (R C : Nat → Nat) (n : Nat) (c : Bool) : Bool :=
  rankB Nat.beq mulP (clsL C n c) (repT R C n c)

end CFSG.KD.G22C

end
