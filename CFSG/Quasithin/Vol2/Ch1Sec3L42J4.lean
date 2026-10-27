module

public import CFSG.Quasithin.Background.A3Structure312Defs

public section

namespace CFSG.Quasithin.L139L42

open CFSG.Open CFSG.Quasithin CFSG.Blueprint

@[expose] def FactJ4L42Inner : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* NativeSporadic.Carrier .J4) →
    ∀ B : Subgroup X, IsPSL 4 2 1 (ModO2 B) → ∀ t ∈ Subgroup.normalizer (B : Set X),
      ∃ b ∈ B, ∀ x ∈ B, (t * x * t⁻¹)⁻¹ * (b * x * b⁻¹) ∈ pCoreOf 2 B

end CFSG.Quasithin.L139L42
