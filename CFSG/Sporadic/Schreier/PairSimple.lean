module

public import Mathlib.GroupTheory.Subgroup.Simple

public section

namespace CFSG.Sporadic.Schreier

theorem isSimpleGroup_of_mulEquiv_perm {G : Type*} [Group G] (hG : IsSimpleGroup G) {n : ℕ}
    {P : Subgroup (Equiv.Perm (Fin n))} (e : G ≃* P) : IsSimpleGroup P :=
  e.symm.isSimpleGroup

end CFSG.Sporadic.Schreier
