module

public import Certificates.Data.Kernel.Census.PackedConj

public section

namespace CFSG.KC.Census

open CFSG.KC.Enum

section Checks

variable (n w : Nat)

@[expose] noncomputable def pwitF (ps : List Nat) (inX outX : Nat → Bool)
    (allowPW allowInX allowU : Bool) (basis : Array Nat) (cE : ArrCertP) (cs : Array ArrCertP)
    (aux : Nat × Nat) : WitP → Bool
  | .order4 [⟨e, [⟨t, c₁, c₂⟩]⟩] m =>
    let T := pmask n w basis t
    let E := pmask n w basis e
    let Y := ppow n w (pc n w E (pc n w aux.1 (pc n w E aux.2))) m
    inX c₁ && inX c₂ && !(Nat.beq T (pid n w)) && pcommA n w c₁ T && pcommA n w c₂ T &&
      Nat.beq (pc n w aux.1 (pc n w c₂ c₁)) (pc n w c₁ c₂) &&
      Nat.beq (pc n w aux.2 aux.1) (pid n w) && Nat.beq (pc n w E E) (pid n w) &&
      !(Nat.beq (pc n w Y Y) (pid n w)) && Nat.beq (pc n w (pc n w Y Y) (pc n w Y Y)) (pid n w)
  | wt => pwitOK n w ps inX outX allowPW allowInX allowU basis cE cs wt

@[expose] noncomputable def penumF (basis : Array Nat) (ps : List Nat) : Bool :=
  ((List.range basis.size).all fun k => Nat.beq (pc n w basis[k]! basis[k]!) (pid n w)) &&
    ((List.range basis.size).all fun k => (List.range k).all fun l =>
      pcommA n w basis[k]! basis[l]!) &&
    asc (((pmaskCert n w basis).pts.toList.map (pkey n w ps)).insertionSort (· ≤ ·))

@[expose] noncomputable def pcHeadA (x : Nat) (l : List Nat) (r : Nat) (c : List Nat) : Bool :=
  pvalid n w x && Nat.beq (pc n w x x) (ppcA n w l r) && Nat.beq c.length l.length &&
    (l.zip c).all (fun yc => Nat.beq (pc n w yc.1 x) (pc n w x (ppcA n w l yc.2)))

@[expose] noncomputable def pcHeadB (x : Nat) (l : List Nat) (b : Nat × Nat) : Bool :=
  Nat.blt b.2 n && b.1.testBit b.2 && !(b.1.testBit (at' w x b.2)) &&
    l.all (fun y => (List.range n).all fun p => !(b.1.testBit p) || b.1.testBit (at' w y p))

@[expose] noncomputable def ppcHeadAt : List Nat → List Nat → List (List Nat) → List (Nat × Nat) →
    Bool
  | [], _, _, _ => true
  | x :: l, r :: _, c :: _, b :: _ => pcHeadA n w x l r c && pcHeadB n w x l b
  | _, _, _, _ => false

end Checks

end CFSG.KC.Census
