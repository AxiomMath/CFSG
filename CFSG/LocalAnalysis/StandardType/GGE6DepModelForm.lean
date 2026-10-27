module

public import CFSG.LocalAnalysis.StandardType.GGE6DepModelDefs

public section

namespace CFSG.StandardType

namespace E6Dep

theorem gensAll_isometry (t w : ZMod 3) (h : t * w = 2) (i : Fin 7) :
    (gensAll 0 t 0 w i).transpose * gram6 * gensAll 0 t 0 w i = gram6 := by
  have key : ∀ t w : ZMod 3, t * w = 2 → ∀ i : Fin 7,
      (gensAll 0 t 0 w i).transpose * gram6 * gensAll 0 t 0 w i = gram6 := by
    decide +kernel
  exact key t w h i

end E6Dep

end CFSG.StandardType

end
