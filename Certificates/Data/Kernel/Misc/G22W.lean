module

public import Certificates.Data.Kernel.Misc.BfsK
public import Certificates.Data.Kernel.Mat8P
public import Certificates.Data.Kernel.G2Three.Defs

public section

namespace CFSG.KD.G22W

open CFSG.KD.BfsK CFSG.KC.Mat8P CFSG.KC.Loop

@[expose] noncomputable def numX (R : Nat → Nat) (t : Nat) : Nat := recX R 2 t

@[expose] noncomputable def posQ (R : Nat → Nat) (t : Nat) (g : Bool) : Nat :=
  recF R 2 (Bool.rec (motive := fun _ => Nat) 1 0 g) t

@[expose] def stepI (Q : Nat → Bool → Nat) (t : Nat) :
    Nat × Bool × List Nat × List Nat → Bool → Nat × Bool × List Nat × List Nat
  | (c, ok, acc, fr), g =>
    cond (Nat.blt (Q t g) c) (c, ok, acc, fr)
      (cond (Nat.beq (Q t g) c) (Nat.add c 1, ok, Q t g :: acc, Q t g :: fr)
        (Nat.add c 1, false, acc, fr))

@[expose] def runI (Q : Nat → Bool → Nat) :
    List Nat → Nat × Bool × List Nat × List Nat → Nat × Bool × List Nat × List Nat
  | [], st => st
  | t :: l, st =>
    match stepI Q t (stepI Q t st true) false with
    | (c, ok, acc, fr) => runI Q l (c, ok, acc, fr)

@[expose] def bfsI (Q : Nat → Bool → Nat) :
    Nat → Nat → Bool → List Nat → List Nat → Bool × List Nat
  | 0, _, ok, acc, _ => (ok, acc)
  | fuel + 1, c, ok, acc, fr =>
    match fr with
    | [] => (ok, acc)
    | _ =>
      match runI Q fr (c, ok, acc, []) with
      | (c', ok', acc', fr') => bfsI Q fuel c' ok' acc' fr'

@[expose] def isDesc : List Nat → Nat → Bool
  | [], n => Nat.beq n 0
  | _ :: _, 0 => false
  | x :: l, n + 1 => Nat.beq x n && isDesc l n

@[expose] noncomputable def searchK (R : Nat → Nat) (n : Nat) : Bool :=
  Nat.beq (numX R 0) oneP &&
    (fun r : Bool × List Nat => r.1 && isDesc r.2 n) (bfsI (posQ R) 200 1 true [0] [0])

@[expose] def goodK (x : Nat) : Bool :=
  Nat.blt (Nat.land x (nat_lit 255)) (nat_lit 64) &&
    Nat.blt (Nat.land (Nat.shiftRight x (nat_lit 8)) (nat_lit 255)) (nat_lit 64) &&
    Nat.blt (Nat.land (Nat.shiftRight x (nat_lit 16)) (nat_lit 255)) (nat_lit 64) &&
    Nat.blt (Nat.land (Nat.shiftRight x (nat_lit 24)) (nat_lit 255)) (nat_lit 64) &&
    Nat.blt (Nat.land (Nat.shiftRight x (nat_lit 32)) (nat_lit 255)) (nat_lit 64) &&
    Nat.blt (Nat.land (Nat.shiftRight x (nat_lit 40)) (nat_lit 255)) (nat_lit 64) &&
    Nat.beq (Nat.land (Nat.shiftRight x (nat_lit 48)) (nat_lit 255)) (nat_lit 64) &&
    Nat.beq (Nat.land (Nat.shiftRight x (nat_lit 56)) (nat_lit 255)) (nat_lit 128)

@[expose] noncomputable def prodK (R : Nat → Nat) (n hi : Nat) : Bool :=
  allBelow n hi fun t =>
    goodK (numX R t) &&
      Nat.blt (posQ R t true) n && Nat.beq (mulP (R 0) (numX R t)) (numX R (posQ R t true)) &&
      Nat.blt (posQ R t false) n && Nat.beq (mulP (R 1) (numX R t)) (numX R (posQ R t false))

@[expose] noncomputable def sortX (R : Nat → Nat) (n hi : Nat) : Bool :=
  CFSG.KD.G2Three.sortK (numX R) (recF R 2 2) (recF R 2 3) n hi

@[expose] noncomputable def witAt (R : Nat → Nat) (o₂ k v : Nat) : Nat :=
  Nat.land (Nat.shiftRight (R (Nat.add o₂ k)) (Nat.mul 14 v)) 16383

@[expose] def mvK (x v : Nat) : Nat := mv8R (unpackM x) v

@[expose] noncomputable def witOK (R : Nat → Nat) (n x v γ : Nat) : Bool :=
  Nat.blt γ n && Nat.beq (mvK (numX R γ) v) v &&
    !(Nat.beq (mulP (numX R γ) x) (mulP x (numX R γ)))

@[expose] noncomputable def stabK (R : Nat → Nat) (o₂ n hi : Nat) : Bool :=
  allBelow n hi fun t =>
    cond (Nat.beq (mulP (numX R t) (numX R t)) oneP && !(Nat.beq (numX R t) oneP))
      (allBelow 64 1 fun v => Nat.beq v 0 || !(Nat.beq (mvK (numX R t) v) v) ||
        witOK R n (numX R t) v (witAt R o₂ (recF R 2 4 t) v))
      true

end CFSG.KD.G22W

end
