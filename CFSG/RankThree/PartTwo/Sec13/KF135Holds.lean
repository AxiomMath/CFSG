module

public import CFSG.RankThree.PartTwo.Sec13.KF135Fam1
public import CFSG.RankThree.PartTwo.Sec13.KF135Fam3
public import CFSG.RankThree.PartTwo.Sec13.KF135Fam4
public import CFSG.RankThree.PartTwo.Sec13.KF135Alt
public import CFSG.RankThree.PartTwo.Sec13.KF135Spor
public import CFSG.RankThree.PartTwo.Sec13.KF135Chev2
public import CFSG.RankThree.PartTwo.Sec13.KF135Fam8
public import CFSG.RankThree.PartTwo.Sec13.KF135Fam9
public import CFSG.RankThree.PartTwo.Sec13.K135OutPFinal
public import CFSG.RankThree.PartTwo.Sec13.K135SFGL12Final
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.OddSporadicHolds

public section

namespace CFSG.RankThree.PartTwo.Sec13.KF135Proof

theorem kF135_holds :
    F135Last.KF135 :=
  kF135_of_families kF135At_fam1 kF135At_fam2 kF135At_fam3 kF135At_fam4 kF135At_fam5
    (kF135At_fam6 CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
      CFSG.ComponentClassification.CatFC.card_carrier_eq_sporOrder_all
      (fun s _ hp hp2 => CFSG.AGLEmbedding.not_dvd_card_outer_sporadic
        CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group s _ hp hp2))
    KF135Chev2.kF135At_fam7 (kF135At_fam8 F135Last.kFactOutP_holds) kF135At_fam9

end CFSG.RankThree.PartTwo.Sec13.KF135Proof

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

theorem item135A7OneTwoCrit2_of_gl12
    (hMPG : K135SF.KFactMultPrimeGL12) (hOG : K135SF.KFactOutGL12) (hKFG : K135SF.KF135GL12) :
    Item135A7OneTwoCrit2 :=
  item135A7OneTwoCrit2_of_kf135_gl12_closed KF135Proof.kF135_holds hMPG hOG hKFG

end CFSG.RankThree.PartTwo.Sec13.F135Last
