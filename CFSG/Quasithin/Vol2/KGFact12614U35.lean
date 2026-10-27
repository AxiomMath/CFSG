module

public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.H13

open CFSG.Quasithin

@[expose] def FactU35A6Cent : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsPSU 3 5 1 Q →
    ∀ (α : MulAut Q) (H : Subgroup Q), IsAlt 6 ↥H → (∀ h ∈ H, α h = h) →
      (∃ n : ℕ, α ^ 2 ^ n = 1) → α = 1

end CFSG.Quasithin.H13
