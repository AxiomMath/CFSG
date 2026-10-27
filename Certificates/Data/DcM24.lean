module

public import Certificates.Data.DcRank
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBaseNative

public section

namespace CFSG.Quasithin.H13.LocDbl.DcM24

open CFSG.Quasithin.H13.LocDbl.DcNative
open CFSG.QuasithinUnique.K1.SporadicPerm (slpTabsA)

@[expose] def ta : Array Nat :=
  #[3, 6, 16, 0, 12, 8, 1, 14, 5, 18, 17, 20, 4, 15, 7, 13, 2, 10, 9, 23, 11, 22, 21, 19]

@[expose] def tb : Array Nat :=
  #[3, 20, 8, 5, 17, 0, 6, 7, 14, 4, 10, 11, 16, 1, 2, 12, 15, 9, 23, 19, 13, 21, 18, 22]

end CFSG.Quasithin.H13.LocDbl.DcM24
