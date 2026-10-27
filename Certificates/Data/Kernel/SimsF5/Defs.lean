module

public import CFSG.Certificates.Kernel.Orders.Mat

public section

namespace CFSG.KC.SimsF5

open CFSG.KC.Ord

@[expose] noncomputable def l6L : Nat :=
  1671623677278685503141555994978895751093572942865858908798586945

@[expose] noncomputable def l6H : Nat :=
  53491957672917936100529791839324664034994334171707485081554782240

@[expose] noncomputable def l6CM : Nat := 96547219075955945024103736637267007212033175418715504703

@[expose] noncomputable def l6RM : Nat := 68719476735

@[expose] noncomputable def l6ONE : Nat :=
  1645504557321580186574125978775002378553869913044102104863473665

@[expose] noncomputable def l6LV : Nat := 1090785345

@[expose] noncomputable def l6HV : Nat := 34905131040

@[expose] noncomputable def m6 (A B : Nat) : Nat := mulR 3 6 36 6 3 l6L l6H l6CM l6RM A B

end CFSG.KC.SimsF5

end
