module

public import CFSG.RankThree.PartTwo.Sec20.SimsItem201Foote
public import CFSG.CGT.Stroth77.StrothSigma6Holds
public import CFSG.RankThree.PartTwo.Sec15.Lempken155L3Cover
public import CFSG.RankThree.PartTwo.Sec19.Ronan1914Leaves316

public section

namespace CFSG.RankThree.PartTwo.Sec19.Ronan1914

section Lemma316


theorem item316_of_310 (h310 : Sec6.Item3_10) : Item316 :=
  item316_of_stroth CFSG.CGT.Stroth77.strothSigma6_holds h310

end Lemma316

section Steps


theorem step1914_of_310
    (h310 : Sec6.Item3_10) : Step1914 :=
  step1914_of_leaves316 (Sec15.item1730_of_316_310 (item316_of_310 h310) h310)
    (item316_of_310 h310)

theorem step1918_of_310
    (h310 : Sec6.Item3_10) : Step1918 :=
  step1918_of_leaves316 (Sec15.item1730_of_316_310 (item316_of_310 h310) h310)
    (item316_of_310 h310)

end Steps

end CFSG.RankThree.PartTwo.Sec19.Ronan1914
