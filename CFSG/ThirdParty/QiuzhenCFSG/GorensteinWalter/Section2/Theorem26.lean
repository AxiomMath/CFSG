module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Theorem26Core
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Theorem26ComponentTrivial

namespace CFSG
end CFSG
open CFSG

/-!
# Theorem 2.6 (Bender, "Finite Groups with Dihedral Sylow 2-Subgroups")

Wrapper: the branch facts live in `Theorem26Core`, and the
trivial-`O₂(Ĥ)` component-lane contradiction lives in
`Theorem26ComponentTrivial`.  This module assembles the final public
statement.
-/

namespace CFSG.GorensteinWalter

universe u

/-- Theorem 2.6 (Bender, *Finite Groups with Dihedral Sylow 2-Subgroups*,
p. 220): `U = O(Ĥ)`, `C_S(U) = O₂(Ĥ)`, and either the first or the second
structure alternative holds. -/
public theorem theorem_2_6
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) :
    CentralizerStructure c := by
  by_cases hO2 : twoCoreOf c.Hhat ≠ ⊥
  · exact theorem_2_6_branch_one hmin c hO2
  · have hO2bot : twoCoreOf c.Hhat = ⊥ := not_not.mp hO2
    have hE : componentLayerOf c.Hhat = ⊥ :=
      theorem_2_6_component_trivial hmin c hO2bot
    exact theorem_2_6_structure_of_component_trivial hmin c hE

end CFSG.GorensteinWalter
