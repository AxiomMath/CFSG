module

public import CFSG.Quasithin.Vol2.Ch3B513NSp4
public import CFSG.Quasithin.Vol2.Ch3B513NG2
public import CFSG.Quasithin.Vol2.Ch3B513NG2Two
public import CFSG.Quasithin.Vol2.Ch3B513NC1W5
public import CFSG.Quasithin.Vol2.Ch3B513NC1Lin
public import CFSG.Quasithin.Background.F918F3

public section

namespace CFSG.Quasithin.B513N

open CFSG.Assembly.LowTwoRank


theorem case1_holds (hA21 : AsA21SQTKSection) (hI16 : H13.AsI16Cover328)
    (hA8 : AsI16CoverA8) (hIdent : AsB42Ident) (h42 : AsB42) : Case1 :=
  case1_of hA21 hI16 hA8 c1sp4_holds (c1g2_holds hIdent h42 hA21 c1g2Der_holds) c1g2Der_holds
    c1wedge5_holds c1g2Two_holds c1ii_holds c1iii_holds c1iv_holds

theorem case1_of_b42
    (hA21 : AsA21SQTKSection) (h42 : AsB42) : Case1 :=
  case1_holds hA21 H13.VolI.asI16Cover328_holds asI16CoverA8_of (FFC.asB42Ident_of_b42 h42)
    h42

end CFSG.Quasithin.B513N
