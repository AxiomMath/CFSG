module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreDefs
import CFSG.LocalAnalysis.StandardType.GGQ2ExcTwE6Placement
import CFSG.LocalAnalysis.StandardType.GGQ2ExcTwE6Cover
import CFSG.LocalAnalysis.StandardType.GGQ2ExcTwE6RankFive
import CFSG.LocalAnalysis.StandardType.GGQ2ExcModelFrameEquivCover
import CFSG.LocalAnalysis.StandardType.GGQ2ExcTwE6Transport
import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreCent
import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreNormalizer
import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreAmbient

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

theorem excTwE6Placement_of_core
    (hO2 : ExcCoreOccurs 2 .E6) (hM2 : ExcCoreMarked 2 .E6) (hI2 : ExcCoreInside 2 .E6)
    (hO3 : ExcCoreOccurs 3 .E6) (hM3 : ExcCoreMarked 3 .E6) (hI3 : ExcCoreInside 3 .E6) :
    ExcTwE6Placement :=
  excTwE6Placement_of_pieces excTwE6Cover_holds excTwE6RankFive_holds
    (excTwE6ModelFrame_of_core hO2 hM2 excCoreCent_E6_two hI2 excCoreNormalizer_E6_two
      excCoreAmbient_E6_two hO3 hM3 excCoreCent_E6_three hI3 excCoreNormalizer_E6_three
      excCoreAmbient_E6_three)
    modelFrameOfEquivCover_holds

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
