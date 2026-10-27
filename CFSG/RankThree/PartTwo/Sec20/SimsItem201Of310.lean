module

public import CFSG.RankThree.PartTwo.Sec20.SimsItem201Foote
public import CFSG.RankThree.PartTwo.Sec15.Lempken155L3Cover
public import CFSG.RankThree.GF2n.Item310Bridges
public import CFSG.CGT.Stroth77.StrothSigma6Holds

public section

namespace CFSG.RankThree.PartTwo.Sec19

theorem item316_of_stroth_gf2n
    (hStroth : CFSG.OddStandard.HigherRank.YamadaG23.StrothSigma6)
    (hGF : CFSG.RankThree.GF2n.GF2nTypeStatement) :
    Item316 :=
  item316_of_stroth hStroth (CFSG.RankThree.GF2n.item3_10_of_gf2nTypeStatement hGF)

end CFSG.RankThree.PartTwo.Sec19

namespace CFSG.RankThree.PartTwo.Sec17

theorem item1730_of_stroth_310
    (hStroth : CFSG.OddStandard.HigherRank.YamadaG23.StrothSigma6)
    (h310 : Sec6.Item3_10) :
    Item1730 :=
  Sec15.item1730_of_316_310 (Sec19.item316_of_stroth hStroth h310) h310

theorem item1730_of_stroth_gf2n
    (hStroth : CFSG.OddStandard.HigherRank.YamadaG23.StrothSigma6)
    (hGF : CFSG.RankThree.GF2n.GF2nTypeStatement) :
    Item1730 :=
  item1730_of_stroth_310 hStroth (CFSG.RankThree.GF2n.item3_10_of_gf2nTypeStatement hGF)

end CFSG.RankThree.PartTwo.Sec17

namespace CFSG.RankThree.PartTwo.Sec20

theorem item201Contra1_of_stroth_310
    (hStroth : CFSG.OddStandard.HigherRank.YamadaG23.StrothSigma6)
    (h310 : Sec6.Item3_10) :
    Item201Contra1 :=
  item201Contra1_of_stroth (Sec17.item1730_of_stroth_310 hStroth h310) h310 hStroth

theorem item201Contra1_of_stroth_gf2n
    (hStroth : CFSG.OddStandard.HigherRank.YamadaG23.StrothSigma6)
    (hGF : CFSG.RankThree.GF2n.GF2nTypeStatement) :
    Item201Contra1 :=
  item201Contra1_of_stroth_310 hStroth (CFSG.RankThree.GF2n.item3_10_of_gf2nTypeStatement hGF)

end CFSG.RankThree.PartTwo.Sec20

namespace CFSG.RankThree.PartTwo.Sec19

theorem item316_of_gf2n
    (hGF : CFSG.RankThree.GF2n.GF2nTypeStatement) :
    Item316 :=
  item316_of_stroth_gf2n CGT.Stroth77.strothSigma6_holds hGF

end CFSG.RankThree.PartTwo.Sec19

namespace CFSG.RankThree.PartTwo.Sec17

theorem item1730_of_gf2n
    (hGF : CFSG.RankThree.GF2n.GF2nTypeStatement) :
    Item1730 :=
  item1730_of_stroth_gf2n CGT.Stroth77.strothSigma6_holds hGF

end CFSG.RankThree.PartTwo.Sec17

namespace CFSG.RankThree.PartTwo.Sec20

theorem item201Contra1_of_gf2n
    (hGF : CFSG.RankThree.GF2n.GF2nTypeStatement) :
    Item201Contra1 :=
  item201Contra1_of_stroth_gf2n CGT.Stroth77.strothSigma6_holds hGF

end CFSG.RankThree.PartTwo.Sec20
