module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExtNbrBridge
public import CFSG.LocalAnalysis.StandardType.GGQ2ExtClassicalStatements
public import CFSG.LocalAnalysis.StandardType.GGQ2NoTwoNodeExc

public section

namespace CFSG.StandardType.GGQ2Frame

theorem ggQ2ExtCoverInput_of_statements (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hrig : GGLabelRigidInput) (hD5 : ∀ R, ExtD5Bridge R)
    (hpCl : PlacementInputOn ClassicalLabel (catalogueOf classicalCatalogue excCatalogue))
    (hpEx : PlacementInputOn ExceptionalLabel (catalogueOf classicalCatalogue excCatalogue))
    (hpSm : PlacementInputOn SmallLabel (catalogueOf classicalCatalogue excCatalogue))
    (hlin : ExtCasesLin) (hsymp : ExtCasesSymp) (horth : ExtCasesOrth)
    (hunF : ExtCasesUnitFull) (hunH : ExtCasesUnitHeart) (hexc : ∀ m : Fin 6, ExtCases (excRaw m)) :
    GGQ2ExtCoverInput := by
  refine ggQ2ExtCoverInput_of_cases hLB hP hrig extNbrBridge hD5
    (catalogueOf classicalCatalogue excCatalogue)
    (placementInput_of_split _ hpCl hpEx hpSm) fun k => ?_
  by_cases hk : IsClassical k
  · rw [catalogueOf_classical classicalCatalogue excCatalogue hk]
    cases k with
    | lin t ε => exact hlin t ε
    | symp t => exact hsymp t
    | orth t δ => exact horth t δ
    | unitFull N => exact hunF N
    | unitHeart N => exact hunH N
    | exceptional m => exact absurd hk (by simp [IsClassical])
  · have hk' : IsExceptional k := hk
    rw [catalogueOf_exceptional classicalCatalogue excCatalogue hk']
    cases k with
    | exceptional m => exact hexc m
    | _ => exact absurd trivial hk

end CFSG.StandardType.GGQ2Frame

end
