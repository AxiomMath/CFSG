module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def FactM22HexadAut : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* ↥NativeSporadic.M22) →
    ∀ (B E : Subgroup X), Nat.card ↥B = 5760 → E ≤ B → B ≤ Subgroup.normalizer (E : Set X) →
      Nat.card ↥E = 16 → ∀ α : MulAut X, (∀ e ∈ E, α e = e) → ∃ e ∈ E, α = MulAut.conj e

end CFSG.Quasithin.H13
