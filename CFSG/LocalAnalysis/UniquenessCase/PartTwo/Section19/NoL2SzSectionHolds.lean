module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NoL2SzSectionOfNormal
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NoL2SzSectionNormality
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.NoL2SzSection

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

theorem k_19_25_noL2SzSection_holds :
    K_19_25_noL2SzSection :=
  fun Q _ _ p Y hp hp2 hFY hO hY N hN n hn =>
    k_19_25_noL2SzSection_of_normal Q p Y hp hp2
      (normal_of_r72Shape_of_isStronglyPEmbedded hp hp2 hFY hO hY hN) hFY hO hY N hN n hn

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
