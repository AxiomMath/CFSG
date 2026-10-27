module

public import CFSG.Milestones.ASVolI.F437U.U5D
public import CFSG.Milestones.ASVolI.F429
public import CFSG.Milestones.ASVolI.F435
public import CFSG.Milestones.ASVolI.F431.RonanOddU4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF

theorem burnsideF437U_sylowInputDegIII_U4_of_fourII (h : F437FourIIU4) :
    burnsideF437_SylowInputDegIII .U4 1 := by
  intro E _ Gp M₁ M₂ Y _ β M _ ε z hyp Tb hTb fb hfbT hfbS hsq _ hiii hsyl
  by_cases hS : ChF.IsSylowOf 2 (imB β ε Tb ⊓ Subgroup.centralizer ({bM β ε fb} : Set M))
      (Subgroup.centralizer ({bM β ε fb} : Set M))
  · exact Or.inl hS
  · exact Or.inr ⟨rfl, rfl, h E Gp M₁ M₂ Y β M ε z hyp Tb hTb fb hfbT hfbS hsq hiii hsyl hS⟩

section Top

set_option linter.unusedSectionVars false

theorem burnsideF437U_F437KindDeg_U5 : burnsideF437_F437KindDeg .U5 1 :=
  burnsideF437_F437KindDeg_of ChF.nativeChartCompatibility
    (burnsideF437_classInputDeg_of_F_4_29 as_F_4_29 .U5 1 ⟨by decide, by decide⟩)
    burnsideF437U_fixedInputDeg_U5
    (burnsideF437_sylowInputDeg_U5
      (burnsideF437_classInputDeg_of_F_4_29 as_F_4_29 .U5 1 ⟨by decide, by decide⟩)
      (burnsideF437_F435U5_of_F_4_35 as_F_4_35) burnsideF437U_u5DataInput)

theorem burnsideF437U_F437KindDeg_U4_of_fourII (h : F437FourIIU4) :
    burnsideF437_F437KindDeg .U4 1 :=
  burnsideF437_F437KindDeg_ofIII ChF.nativeChartCompatibility
    (burnsideF437_classInputDeg_of_F_4_29 as_F_4_29 .U4 1 ⟨by decide, by decide⟩)
    burnsideF437U_fixedInputDeg_U4 (burnsideF437U_sylowInputDegIII_U4_of_fourII h)

theorem burnsideF437U_F_4_37_of_fourII (h : F437FourIIU4) : F_4_37 :=
  burnsideF437_F_4_37_of_U4_U5 (burnsideF437U_F437KindDeg_U4_of_fourII h)
    (burnsideF437_classInputDeg_of_F_4_29 as_F_4_29 .U5 1 ⟨by decide, by decide⟩)
    burnsideF437U_fixedInputDeg_U5 (burnsideF437_F435U5_of_F_4_35 as_F_4_35)
    burnsideF437U_u5DataInput

end Top

end CFSG.ASVolI
