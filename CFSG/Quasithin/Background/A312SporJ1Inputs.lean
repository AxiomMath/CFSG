module

public import CFSG.Quasithin.Background.E2TwoProofSporJ1Inputs

public section

namespace CFSG.Quasithin.A312S.J1

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm
  CFSG.Quasithin.E2P.SporB.J1Lat

@[expose] def j1CentWords : List (Nat × List Nat) :=
  [(1, [1]), (2, [0, 1]), (3, [0, 2]), (4, [2]), (5, [1, 2]), (6, [0, 1, 2]), (9, [0])]

@[expose] def j1STab (w : List Nat) : Array Nat := wordTabA j1STabs.toArray 1540 w

end CFSG.Quasithin.A312S.J1
