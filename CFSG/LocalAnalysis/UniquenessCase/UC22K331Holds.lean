module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K331Chev2
public import CFSG.LocalAnalysis.UniquenessCase.UC22K331SporSmall
import CFSG.RankThree.PartOne.TCB.Sporadic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3

theorem k331Residue_holds :
    K331Residue :=
  k331_chev2.union (k331_sporSmall CFSG.RankThree.PartOne.TCB.nonempty_carrier_mulEquiv_group)

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3
