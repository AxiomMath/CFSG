module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.Quasithin

variable {G : Type} [Group G]

@[expose] def IsThreePrimeGroup (X : Subgroup G) : Prop := ¬ 3 ∣ Nat.card X

end CFSG.Quasithin
