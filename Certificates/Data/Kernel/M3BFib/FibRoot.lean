module

public import Certificates.Data.Kernel.M3BFib.Fib

public section

namespace CFSG.KC.M3BF

open Timmesfeld.M3B (AD vget aget nfD eOf B0 fRootV)

@[expose] noncomputable def pdOf (D : AD) : PD :=
  ((List.finRange 12).map fun i => enc ((List.finRange 12).map fun j => (vget (aget D i).1 j).val),
    (List.finRange 12).map (fun i => (aget D i).2.val), D.2.val)

@[expose] noncomputable def lamChk (gs : List GenK) : Bool :=
  gs.all fun g => Nat.blt g.2.1.2.2 3 && Nat.blt g.2.2.1.2.2 3

@[expose] noncomputable def rootVChk (Lp : List Nat) (T : PD) (k : Nat) (rs : List (Nat × Nat)) :
    Bool :=
  rs.all fun r => (fRootV k).any fun v =>
    pdEq (compK Lp T (pdOf (nfD (B0 ()) (eOf v 0)))) (T.1, dig3 r.1, T.2.2)

end CFSG.KC.M3BF

end
