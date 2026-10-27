module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalResHeadsThree
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherExcG2
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherExcFixTwE6
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherExcTriD4
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherExcTwF4

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggNbrInnerWeylOn_c9_holds
    (hL : GGLBalanceInput) (hPJ : GGStdSubPrimeInput) (hG : GGNbrGraphInput)
    (hpc : GGRawPCyclicOn GGNotD4Three) (hconj : GGRawFieldConjInputExc)
    (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput) :
    GGNbrInnerWeylOn fun p lab => GGNbrWeylFieldOtherOpenLabel p lab ∧
      ¬ GGFieldFixLabel p lab ∧ ¬ GGFieldFixNsLabel p lab ∧ ¬ GGFieldFixD4Label p lab ∧
      ¬ (p = 3 ∧ lab.tag = .G2 ∧ 6 ∣ lab.n) :=
  ggNbrInnerWeylOn_c9_of_nonClassical hL hPJ hG hpc hconj hcen hinn
    (ggNbrInnerWeylOn_c9NonClassical_of_kLevel hL hPJ hG hpc hconj hcen hinn ggFieldFixKnown_twE6
        (ggFieldKLevel_G2Dvd hpc hconj hcen hinn) (ggFieldKLevel_triD4Dvd hpc hconj hcen hinn)
        (ggFieldKLevel_twF4Add hpc hconj hcen hinn))

end CFSG.StandardType

end
