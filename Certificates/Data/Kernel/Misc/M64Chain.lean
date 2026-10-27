module

public import Certificates.Data.Kernel.Spor.Raw

public section

namespace CFSG.KC.Misc.M64

open CFSG.KC.Enum

@[expose] def dM64 : List (List Int) := []

@[expose] noncomputable def relK (n w m idn : Nat) (U : Nat → Nat) (r : List (Fin 5 × Bool)) :
    Nat :=
  r.foldl (fun acc l => pcomp n w m acc (cond l.2 (U l.1.val) (U (5 + l.1.val)))) idn

@[expose] def invW (w : List Int) : List Int := (w.map fun l => -l).reverse

end CFSG.KC.Misc.M64

end
