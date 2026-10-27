module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312Rest2J4
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2Main
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4OvMain

public section

namespace CFSG.Quasithin.Vol2.Ch10


theorem a312ListFactsCat_holds
    : QuasithinUnique.Vol2Native.A312ListFactsCat :=
  QuasithinUnique.Vol2Native.A312L.a312ListFactsCat_of_families
    QuasithinUnique.Vol2Native.threeCoverFactCat
    (QuasithinUnique.Vol2Native.A312L.a312Families_of_residual (A38c14.A312ResidualRest.toResidual
      (A38c15.A312ResidualRest10.toRest (A38c17.A312ResidualRest7.toRest10 A312J2.famJ2_holds
      (A38c17.A312ResidualRest6.toRest7 (A38c17.A312ResidualRest4.toRest6
      (A38c17.A312ResidualRest3.toRest4 (A38c17.A312ResidualRest2.toRest3
      (A38c17.a312ResidualRest2_of_j4 J4Ov.j4OvergroupLocal_holds J4Fam.j4M2Residual)))))))))

end CFSG.Quasithin.Vol2.Ch10
