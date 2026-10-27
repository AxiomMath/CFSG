module

public import CFSG.LocalAnalysis.StandardType.GGL45E67Holds
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeNonToralCentHolds

public section

namespace CFSG.StandardType

theorem ggL45TorusHKnownFormsOn_e67 :
    GGL45TorusHKnownFormsOn GGL45FamE67 :=
  ggL45TorusHKnownFormsOn_e67_of_nonToralThree ggL45E6NonToralThreeCent_holds

end CFSG.StandardType
