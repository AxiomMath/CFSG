module

public import Certificates.Data.Kernel.Census.PackedConj
public import Certificates.Data.Kernel.Census.PackedL

public section

namespace CFSG.KC.Census

open CFSG.KC.Enum

@[expose] def packW (W : Nat) : List Nat → Nat
  | [] => 0
  | x :: l => Nat.add x (Nat.shiftLeft (packW W l) W)

@[expose] def getW (W P k : Nat) : Nat :=
  Nat.land (Nat.shiftRight P (Nat.mul W k)) (Nat.sub (Nat.shiftLeft 1 W) 1)

@[expose] def fitW (W : Nat) (l : List Nat) : Bool := l.all fun x => Nat.blt x (Nat.shiftLeft 1 W)

section Checks

variable (n w : Nat)

@[expose] noncomputable def prootL (nl : List NodeP) (sz : Nat) (C I : Nat → Nat) (nc e u : Nat)
    (r : Nat × Nat) : Bool :=
  Nat.blt r.1 sz && Nat.blt r.2 nc &&
    (match nl.getD r.1 default with
      | ⟨b, _, _⟩ => strictB (pconjT n w (C r.2) (I r.2) u) fun v =>
        (b.toList.all fun x => Nat.beq x v || Nat.beq x e) && (pspanL n w b.toList).any (Nat.beq v))

@[expose] noncomputable def prootsL (W : Nat) (nodes : Array NodeP) (cs ci : Array Nat)
    (l : List (Nat × (Nat × Nat))) : Bool :=
  strictB nodes.size fun sz => strictB cs.size fun nc => strictB (pid n w) fun e =>
    strictB (packW W cs.toList) fun Pc => strictB (packW W ci.toList) fun Pi =>
      l.all fun ur => prootL n w nodes.toList sz (getW W Pc) (getW W Pi) nc e ur.1 ur.2

end Checks

end CFSG.KC.Census
