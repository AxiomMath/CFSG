module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KU3Ident
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KU3CensusU3

import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KU3CensusOdd
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KU3SU3L2FixHolds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.LocalAnalysis.UniquenessCase

theorem kU3Ident_of_fix
    (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) (hK32 : UCK.K32) (hFix : KU3SU3L2Fix) :
    KU3Ident :=
  kU3Ident_of_census hSch hK32 kU3CensusOdd_holds kU3CensusL2_holds (kU3CensusU3_of_fix hFix)

theorem kU3Ident_holds
    (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) (hK32 : UCK.K32) : KU3Ident :=
  kU3Ident_of_fix hSch hK32 kU3SU3L2Fix_holds

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
