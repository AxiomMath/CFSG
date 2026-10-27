module

public import CFSG.RankThree.PartOne.KE.EFamilies
public import CFSG.RankThree.PartOne.KE.EvenE7E8QPlusExclusion

public section

namespace CFSG.RankThree.PartOne.KE

theorem originalE7_of_cyclotomic_endpoints (hE : E7Endpoints) :
    OriginalE7ComponentLocalCoreOddAction :=
  originalE7_of_endpoints evenE7E8QPlusExclusion hE

theorem originalE8_of_cyclotomic_endpoints (hE : E8Endpoints) :
    OriginalE8ComponentLocalCoreOddAction :=
  originalE8_of_endpoints evenE7E8QPlusExclusion hE

end CFSG.RankThree.PartOne.KE
