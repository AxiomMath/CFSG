module

public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.HMathieu

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def pc24 (p q : Nat) : Nat := pcomp 24 5 (mask 5) p q

@[expose] noncomputable def unpk (p : Nat) : Array Nat :=
  ((List.range 24).map fun i => pg 5 (mask 5) p i).toArray

@[expose] noncomputable def vpK (p : Nat) : Bool :=
  Nat.beq (Nat.shiftRight p 120) 0 && (List.range 24).all fun i => Nat.blt (pg 5 (mask 5) p i) 24

@[expose] noncomputable def bfsStep (gens : List Nat) (st : List Nat × List Nat) (x : Nat) :
    List Nat × List Nat :=
  gens.foldl (fun st' g => if st'.1.contains (pc24 g x) then st' else
    (pc24 g x :: st'.1, pc24 g x :: st'.2)) st

@[expose] noncomputable def bfsP (gens : List Nat) : Nat → List Nat → List Nat → List Nat
  | 0, acc, _ => acc
  | _ + 1, acc, [] => acc
  | f + 1, acc, x :: xs =>
    bfsP gens f ((x :: xs).foldl (bfsStep gens) (acc, [])).1
      ((x :: xs).foldl (bfsStep gens) (acc, [])).2.reverse

end CFSG.KC.HMathieu

end
