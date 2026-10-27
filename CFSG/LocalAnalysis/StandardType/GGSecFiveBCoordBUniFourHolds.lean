module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBUniLeaves
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBUniFour
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.CompletionThree

public section

namespace CFSG.StandardType

theorem ggSecFiveBCoordBUniFourInput_holds :
    GGSecFiveBCoordBUniFourInput :=
  ggSecFiveBCoordBUniFourInput_of_completion fun _ _ _ _ _ _ _ _ E hq hK _ _ a ha R hR =>
    CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.exists_normOmega_hom_of_rangeCoherent_three E
      hq hK a ha R hR

end CFSG.StandardType

end
