module

public import CFSG.LocalAnalysis.StandardType.GGNbrKGFieldE6TwE6
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherExcFixTwE6

public section

namespace CFSG.StandardType

theorem ggFieldFixKnownTwE6_holds :
    GGFieldFixKnownTwE6 :=
  fun p lab hp hp2 hlab hS => ggFieldFixKnown_twE6_all p lab hp hp2 hlab hS.1

theorem ggNbrWeylKGInputRestFive_of_three
    (hpc : GGRawPCyclicOn GGNotD4Three) (hconj : GGRawFieldConjInputExc)
    (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput) (h : GGNbrWeylKGInputRestThree) :
    GGNbrWeylKGInputRestFive :=
  ⟨ggNbrKGFieldTwE6ThreeDvd_of_known hpc hconj hcen hinn ggFieldFixKnownTwE6_holds,
    ggNbrKGFieldTwE6AddLarge_of_known hpc hconj hcen hinn ggFieldFixKnownTwE6_holds, h⟩

end CFSG.StandardType
