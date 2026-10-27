module

public import Certificates.Data.Kernel.LocalQT.LatE

public section

namespace CFSG.KC.LQT.L

open CFSG.KC.Ord CFSG.KC.LQT.P

@[expose] noncomputable def tleT (n : Nat) (C : List Lvl) (d : Nat) (MG : List Nat)
    (MW : List (List (List Nat))) (k : Nat) (T : List (List Nat)) (L : Nat) (TG : List Nat) :
    Bool :=
  andB (chainOK n C) (andB (grpT n C (chainF C) MG MW k T L d) (tleC n C (chainF C) TG))

end CFSG.KC.LQT.L

end
