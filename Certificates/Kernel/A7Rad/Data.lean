module

public import Certificates.Data.Kernel.A7Rad.Checks
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_nat_items_gz CFSG.KD.A7Rad "Certificates/Kernel/A7Rad/data/a7rad.items.gz" 16470 12421618934237353935
  LA WA LB WB

public section

namespace CFSG.KD.A7Rad

open CFSG.KC.LQT.P CFSG.KC.A7Rad

@[expose] def R : Nat := 6581914689
@[expose] def F : Nat := 6582009890
@[expose] def GA : Nat := 6509663268
@[expose] def GB : Nat := 6444650533
@[expose] def GC : Nat := 6544328832
@[expose] def GD : Nat := 6479284384

@[expose] noncomputable def D8 : Nat :=
  pk [one 7, R, pow 7 R 2, pow 7 R 3, F, mul 7 R F, mul 7 (pow 7 R 2) F, mul 7 (pow 7 R 3) F]
@[expose] noncomputable def C4 : Nat := pk [one 7, R, pow 7 R 2, pow 7 R 3]
@[expose] noncomputable def V4 : Nat := pk [one 7, pow 7 R 2, mul 7 R F, mul 7 (pow 7 R 3) F]
@[expose] noncomputable def V4' : Nat := pk [one 7, pow 7 R 2, F, mul 7 (pow 7 R 2) F]
@[expose] noncomputable def Z1 : Nat := pk [one 7, pow 7 R 2]
@[expose] noncomputable def Z2 : Nat := pk [one 7, F]
@[expose] noncomputable def Z3 : Nat := pk [one 7, mul 7 (pow 7 R 2) F]
@[expose] noncomputable def Z4 : Nat := pk [one 7, mul 7 R F]
@[expose] noncomputable def Z5 : Nat := pk [one 7, mul 7 (pow 7 R 3) F]
@[expose] noncomputable def Tf : Nat := pk [one 7, F, GA, GB]
@[expose] noncomputable def Tg : Nat := pk [one 7, mul 7 (pow 7 R 2) F, GC, GD]
@[expose] noncomputable def E1 : Nat := pk [one 7]

@[expose] noncomputable def tenM : List Nat :=
  [maskOf D8 8 E1 1, maskOf D8 8 Z1 2, maskOf D8 8 Z2 2, maskOf D8 8 Z3 2, maskOf D8 8 Z4 2,
    maskOf D8 8 Z5 2, maskOf D8 8 C4 4, maskOf D8 8 V4 4, maskOf D8 8 V4' 4, maskOf D8 8 D8 8]

end CFSG.KD.A7Rad

end
