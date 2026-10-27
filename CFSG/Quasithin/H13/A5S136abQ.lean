module

public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.H13.A5

@[expose] def FactL3SylowCenterCyclic : Prop :=
  ∀ (s : Bool) (p e : ℕ), p.Prime → 1 ≤ e → (p ≠ 2 ∨ e = 1) →
    ∀ (X : Type) [Group X] [Finite X], CFSG.Quasithin.IsPSLEps3 s p e X →
      ∀ T : Sylow 2 X, IsCyclic (Subgroup.center ↥(T : Subgroup X))

end CFSG.Quasithin.H13.A5
