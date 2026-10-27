module

public import CFSG.LocalAnalysis.StandardType.GGBstarLIDTwDFieldLabels
public import CFSG.LocalAnalysis.StandardType.GGBstarLIDTwDFieldGamma

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggTwDOmegaFieldInnR_holds : GGTwDOmegaFieldInnR := by
  intro K _ _ n m p b c hK hm hp hpq hbc
  exact LIDTwDF.ggFieldInnR_omegaMinus hK hm hp hpq hbc

section Holds


theorem ggBstarInnerDiagLInputOn_of_le_twDField {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S p lab → GGOrthLTwDFieldLabel p lab) : GGBstarInnerDiagLInputOn S :=
  ggBstarInnerDiagLInputOn_of_le_twDField_of_omega ggTwDOmegaFieldInnR_holds hS

theorem ggBstarInnerDiagLInputOn_twDField_holds :
    GGBstarInnerDiagLInputOn GGOrthLTwDFieldLabel :=
  ggBstarInnerDiagLInputOn_of_le_twDField fun _ _ h => h

end Holds

end CFSG.StandardType
