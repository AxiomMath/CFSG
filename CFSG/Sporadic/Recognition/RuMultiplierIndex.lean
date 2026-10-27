module

public import CFSG.Sporadic.Recognition.RuMultiplierInputs

public section

namespace CFSG.Sporadic.Recognition.RuMultiplier

open CFSG.CosetTable CFSG.Sporadic.Presentation.Ru.Exact

abbrev RuIndexK : Prop :=
  (genSub {r : FreeGroup (Fin gc) | r ∈ ruCover.map FreeGroup.mk}
      (subsetOf gc [0, 2])).FiniteIndex ∧
    (genSub {r : FreeGroup (Fin gc) | r ∈ ruCover.map FreeGroup.mk}
      (subsetOf gc [0, 2])).index ≤ 16240

end CFSG.Sporadic.Recognition.RuMultiplier

end
