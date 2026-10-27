module

public import CFSG.Quasithin.Vol2.KGFactC31LieSylAdjExc
public import CFSG.Quasithin.Vol2.KGFactC31LieSylClass
public import CFSG.Quasithin.Vol2.Ch4Sec2InspM22Main
public import CFSG.Quasithin.Vol2.Ch4Sec2InspM22Ord
public import CFSG.Quasithin.Vol2.Ch4Sec2InspM22InvCent

public section

namespace CFSG.Quasithin.H13.Ch4

theorem ltqtk_holds :
    LTQTK :=
  ltqtk_of_exc (fun S _ _ p _ hp11 h => KGC31.ltqtk_conj2_G2 S p hp11 h) KGC31.lieSylow11Exc_holds

theorem inspBM22Cover_holds :
    InspBM22Cover :=
  inspBM22Cover_of ltqtk_holds qtkOrdNoM22_holds m23InvCentOrd_holds m24InvCentOrd_holds

end CFSG.Quasithin.H13.Ch4

