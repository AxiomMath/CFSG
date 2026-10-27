module

public import CFSG.LocalAnalysis.StandardType.GGL45FixA2Linear
public import CFSG.LocalAnalysis.StandardType.GGL45FixA2Unitary
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45FieldFixOpenDefs
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldUnitary
public import CFSG.LocalAnalysis.StandardType.GGNbrGraphFieldLinear

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly


theorem ggL45FieldFixKnownFormsOpen_holds : GGL45FieldFixKnownFormsOpen := by
  intro p hp hp2 lab hlab hopen
  obtain ⟨hA2, hp3⟩ := hopen
  subst hp3
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hl, hn, hrow⟩ := hA2
  dsimp only at hl hn hrow
  subst hl
  intro Q hQ
  rcases hrow with ⟨rfl, h3⟩ | ⟨rfl, h3⟩
  · exact NbrGraphLinear.recipeLinear_all (fun K _ _ hK => gffa2_linear_kgraw hn hK h3) hQ
  · exact recipeUnitary_and (fun K _ _ hK => gffa2_unitary_kgraw hn hK h3) hQ

end CFSG.StandardType
