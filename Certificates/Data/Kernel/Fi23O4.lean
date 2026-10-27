module

public import Certificates.Data.Kernel.Fi23R.Defs

public section

namespace CFSG.KC.Fi23O4

open CFSG.KC.Enum CFSG.KC.Fi23R

@[expose] noncomputable def fourK (G : Nat → Nat) (x z : List Nat) : Bool :=
  bAnd(eqB G x [43], bAnd(eqB G (x ++ z) (z ++ x),
    bAnd(eqB G (powW 4 z) [], Bool.not (eqB G (z ++ z) []))))

end CFSG.KC.Fi23O4

end
