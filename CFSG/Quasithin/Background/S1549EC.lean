module

public import CFSG.Quasithin.Background.S1549CTop
public import CFSG.Quasithin.Background.S1549DL3
public import CFSG.Quasithin.Background.S1549DA6
public import CFSG.Quasithin.Background.S1549EA
public import CFSG.Quasithin.Background.S1549EB

public section

namespace CFSG.Quasithin

namespace S1549E

open CFSG.Quasithin.S1549C

theorem stage15349Core_of_remaining_inputs
    (h11 : StageLemma14111) (h113 : StageLemma14113) (hB51 : AsB51) (hB42 : AsB42)
    (i1 : Input49I) (i2 : Input49K) (i4 : Input49L)
    (hLnA : LnParabolicOvergroups) (hLnB : LnSumNatDual) (hLnC : LnInvariantParabolic)
    (hEa : ERankOne) (hEb : L2OffenderNatural) : Stage15349Core :=
  stage15349Core_of_named_inputs h11 h113 i1 i2 (input49E_of_named_inputs hEa hEb) i4
    (input49S_of hB51 hB42) (input49L3_of h113 hB51)
    (input49Ln_of_named_inputs h113 hB51 hLnA hLnB hLnC) (input49A6_of h113 hB51 hB42)

end S1549E

end CFSG.Quasithin
