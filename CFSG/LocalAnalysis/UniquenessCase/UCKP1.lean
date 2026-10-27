module

public import CFSG.LocalAnalysis.UniquenessCase.UCK898

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.LocalAnalysis.UniquenessCase.UC22

theorem u3Range : U3Range := by
  intro X _ _ n hX
  have hadm := CFSG.Blueprint.LieModel.admissible hX.2
  obtain ⟨-, h1, -, hne⟩ := hadm
  by_contra hn
  have hn1 : n = 1 := by omega
  subst hn1
  exact hne (by norm_num)

end CFSG.LocalAnalysis.UniquenessCase.UCK
