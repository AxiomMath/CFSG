module

public import CFSG.RankThree.PartTwo.Sec8.Hering611RSp62Cent
public import CFSG.RankThree.PartTwo.Sec8.Hering611RSp62Inner
public import CFSG.RankThree.PartTwo.Sec8.Hering611KFFinal

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

theorem kF611InvolSp62K_holds : KF611InvolSp62K :=
  kF611InvolSp62K_of kF611Sp62Inner_holds Hering611R.kF611Sp62Cent_holds


theorem item82TwoPSL2NineCore_of_narrow_cert'
    (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h49 : Sec4.Item4_9) (h66 : Sec6.Item6_6)
    (h41 : Sec4.Item4_1LargePrime) (h417 : Sec4.Item4_17) (h611 : Sec6.Item6_11_1)
    (hF : KF611InspectField) (hA9 : KF611A9FuseSym) (hJC : KF611J3CoverFuse) (hJ : KF611J3) :
    Item82Proof.Item82TwoPSL2NineCore :=
  item82TwoPSL2NineCore_of_narrow_cert h45 h48 h49 h66 h41 h417 h611 hF kF611InvolSp62K_holds hA9
    hJC hJ

end CFSG.RankThree.PartTwo.Sec8.Hering611
