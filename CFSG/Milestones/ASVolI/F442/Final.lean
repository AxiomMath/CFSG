module

public import CFSG.Milestones.ASVolI.F442.G2
public import CFSG.Milestones.ASVolI.F442.U5
public import CFSG.Milestones.ASVolI.F431.RFinal

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section Final

set_option linter.unusedSectionVars false



theorem burnsideF42g_A42Rest4 : burnsideF4r_A42Rest4 := by
  intro κ f E _ Gp M₁ M₂ Y _ β M _ ε z hyp hL43 hGp hκ
  rcases hκ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact burnsideF42g_A42_G2two hyp hL43 hGp
  · exact burnsideF42g_A42_U5two hyp hL43 hGp

end Final

end CFSG.ASVolI
