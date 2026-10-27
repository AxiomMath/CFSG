module

public import CFSG.Quasithin.H13.NQBlockOriginalRControlled
public import CFSG.Quasithin.H13.NQBlockRadicalEscapeHolds
public import CFSG.Quasithin.H13.NQBlockSimpleAction
public import CFSG.Quasithin.H13.NQBlockWholeAction
public import CFSG.Quasithin.H13.NQTermMixedA5

public section

namespace CFSG.Quasithin.H13.NQBlock

theorem originalRControlledThompson_holds :
    OriginalRControlledThompson :=
  originalRControlledThompson_of stmtOriginalWitnessSingleton_holds

theorem simpleSourceTensorEquality_holds :
    SimpleSourceTensorEquality :=
  simpleSourceTensorEquality_of_mixedA5 NQTerm.mixedA5RankBudget_holds

theorem originalNoNormalSourceYEscapes_holds :
    OriginalNoNormalSourceYEscapes :=
  originalNoNormalSourceYEscapes_of originalRControlledThompson_holds
    controlledThompsonSourceCommutator_holds solvableSourceRankBudget_holds
    simpleSourceTensorEquality_holds

end CFSG.Quasithin.H13.NQBlock
