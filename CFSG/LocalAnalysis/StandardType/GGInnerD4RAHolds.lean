module

public import CFSG.LocalAnalysis.StandardType.GGInnerD4RASelfMarking
public import CFSG.LocalAnalysis.StandardType.GGInnerD4RASelectedMarking
public import CFSG.LocalAnalysis.StandardType.GGInnerD4RALinearBranch
public import CFSG.LocalAnalysis.StandardType.GGInnerD4RAUnitaryBranch
public import CFSG.LocalAnalysis.StandardType.GGInnerD4RAAssembly
public import CFSG.LocalAnalysis.StandardType.GGInnerD4RAContracts
public import CFSG.LocalAnalysis.StandardType.GGInnerD4RegimeDefs
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType.GGInnerD4RAParts

open CFSG CFSG.Assembly CFSG.StandardType

theorem raComponentLabel_holds : S2MathAs51600.RAComponentLabel :=
  raComponentLabel_of_branches (raSelectedMarking_of_self raModelSelfMarking_holds)
    raLinearBranch_holds raUnitaryBranch_holds

theorem ggInnerOnD4RA_holds :
    GGInnerOnD4RA :=
  S2MathAs51600.raInner_of_componentLabel ggLabelRigidInput_holds raComponentLabel_holds

end CFSG.StandardType.GGInnerD4RAParts

end
