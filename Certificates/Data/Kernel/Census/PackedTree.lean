module

public import Certificates.Data.Kernel.Census.PackedConj

public section

namespace CFSG.KC.Census

open CFSG.KC.Enum

variable (n w : Nat)

@[expose] noncomputable def pnodeOKT (ps : List Nat) (inW : Nat → Bool) (d : ConjDataP)
    (cN : Array ArrCertP) (e0 : Array Nat) (i : Nat) : Bool :=
  penumOK n w d.nodes[i]!.basis ps cN[i]! &&
    (d.nodes[i]!.wit.isMono ||
      ((Nat.blt cN[i]!.pts.size 4 || pexcOK n w ps inW e0 cN d.excs i) &&
        pentsOK n w (d.nodes.map NodeP.basis) cN d.us d.cs d.ci d.ents[i]! i))

end CFSG.KC.Census

end
