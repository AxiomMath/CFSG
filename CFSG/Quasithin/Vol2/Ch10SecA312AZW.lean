module

public import CFSG.Quasithin.Vol2.Ch10SecA312AG
public import CFSG.Quasithin.Vol2.Ch10SecA312AM
public import CFSG.Quasithin.Vol2.Ch10SecA312AP
public import CFSG.Quasithin.Vol2.Ch10SecA312AT
public import CFSG.Quasithin.Vol2.Ch10SecA312AU
public import CFSG.Quasithin.Vol2.Ch10SecA312AV
public import CFSG.Quasithin.Vol2.Ch10SecA312AX
public import CFSG.Quasithin.Vol2.Ch10SecA312AZ

public section

namespace CFSG.Quasithin.Vol2.Ch10.A312A

open CFSG.Open CFSG.SectionRank CFSG.Quasithin CFSG.QuasithinUnique

theorem a312AutCent_of_openRJ [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat]

    (hList : Vol2Native.A312ListFactsCat) (h : A312ZCentOpenRJ) : A312AutCent :=
  a312AutCent_of_zcent hList
    (a312ZCentFacts_of a312ZCentL45_holds a312ZCentM22_holds
      (a312ZCentM23_of a312ZCentRestM23_holds) a312ZCentM24_holds (a312ZCentJ4_of h.j4)
      a312ZCentHS_holds (a312ZCentRu_of h.ruA5))

end CFSG.Quasithin.Vol2.Ch10.A312A
