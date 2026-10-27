module

public import Mathlib.GroupTheory.Coxeter.Inversion

public section

namespace CFSG.StandardType

@[expose] def GGF4B3Core : Prop :=
  ∀ (W : Type) [Group W] (cs : CoxeterSystem CoxeterMatrix.F₄ W) (a : Fin 3 → W),
    (∀ i, cs.IsReflection (a i)) → orderOf (a 0 * a 1) = 3 → orderOf (a 1 * a 2) = 4 →
    orderOf (a 0 * a 2) = 2 →
    ∃ H : Subgroup W, H ≠ ⊤ ∧ (∀ i, a i ∈ H) ∧
      ∀ t, cs.IsReflection t → t ∈ H ∨ Subgroup.closure ({a 0, a 1, a 2, t} : Set W) = ⊤

end CFSG.StandardType

end
