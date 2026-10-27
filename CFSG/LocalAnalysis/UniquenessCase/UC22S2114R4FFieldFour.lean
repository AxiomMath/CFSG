module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R4FFieldRestFour
import CFSG.HardMathSupport.Foote.FamilyReduction.ClassicalFive
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R4FFieldRest

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)



theorem s21_14R4FFieldData_dataOfSetup4 {G : Type} [Group G] [Finite G]
    (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) (hPart : PartIAt S.M) :
    S21_14R4FFieldData (UC6.dataOfSetup4 hS hU S) (fun _ _ => True) := by
  apply s21_14R4FFieldData_of_rest CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement
  intro hSg h76 h74 hH c L hL hX hpow l f hl hlr hn3 hBL hfaith hcase hall
    b hbB hbL r hr hr5 hbr hrn hrf hin hu hlin hlow hsp hplus hminus hf4 he6 he7 he8 htw
  by_cases hsix : ∃ m : ℕ, 6 ≤ m ∧ CFSG.Blueprint.LieModel (BarInf L) .PSL m 2 f
  · obtain ⟨m, hm, hmodel⟩ := hsix
    exact (uc22s2114r4f_false_of_psl_six_le_dataOfSetup4 hS hU S hMS hPart h74
      hH c hL hm hmodel hbB hbL hr hr5 hbr hrn hrf hcase hin).elim
  · exact s21_14R4FFieldRest_dataOfSetup4 hS hU S hMS hPart
      hSg h76 h74 hH c L hL hX hpow l f hl hlr hn3 hBL hfaith hcase hall
      b hbB hbL r hr hr5 hbr hrn hrf hin hu hlin hlow hsix hsp hplus hminus hf4 he6 he7 he8 htw

end CFSG.LocalAnalysis.UniquenessCase.UC22
