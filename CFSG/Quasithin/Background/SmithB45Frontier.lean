module

public import CFSG.Quasithin.Background.SmithB45Dispatch
public import CFSG.Quasithin.Background.SmithB42Holds

public section

namespace CFSG.Quasithin

theorem asB45_of_open
    (hD : AsB45DichotomyNat)
    (hD4 : AsB45TrialityD4) (hF4 : AsB45ReeF4) (hG2 : AsB45G2Even) (hL32 : AsB45L32)
    (hL42 : AsB45L42) (hL52 : AsB45L52) (hA6 : AsB45Alt6) (hHA6 : AsB45HatA6)
    (hA7 : AsB45Alt7) (hA5 : AsB45Alt5) (hL2 : AsB45L2Even) (hU3 : AsB45U3Even) (hSz : AsB45Sz)
    (hL3 : AsB45L3Even) (hU33 : AsB45U33) (hSp4 : AsB45Sp4Even) (hM12 : AsB45M12)
    (hHM22 : AsB45HatM22) (hM22 : AsB45M22) (hM23 : AsB45M23) (hM24 : AsB45M24)
    (hJ2 : AsB45J2) : AsB45 :=
  asB45_of_families asB42_holds hD hD4 hF4 hG2 hL32 hL42 hL52 hA6 hHA6 hA7 hA5 hL2 hU3 hSz hL3
    hU33 hSp4 hM12 hHM22 hM22 hM23 hM24 hJ2

end CFSG.Quasithin
