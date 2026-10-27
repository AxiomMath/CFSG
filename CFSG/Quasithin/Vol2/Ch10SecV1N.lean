module

public import CFSG.Quasithin.Background.A3Structure312Defs
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.EmptyFaithfulMultiple.Inputs5

public section

namespace CFSG.Quasithin.Vol2.Ch10

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

@[expose] def C27NoL2pJ1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R M K : Subgroup G),
    EmptyFaithfulMultiple.HypC23Cat H R M → K ∈ cComp H →
    CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) → CharTwo K → ¬ K ≤ M →
    R ≤ Subgroup.normalizer (K : Set G) →
    ∀ (Q : Type) [Group Q], Nonempty (ModO2 K ≃* Q) →
      ((∃ p : ℕ, p.Prime ∧ IsPSL 2 p 1 Q ∧ p ^ 2 % 5 = 1 ∧ (p % 8 = 3 ∨ p % 8 = 5)) ∨
        (∃ p : ℕ, p.Prime ∧ 3 < p ∧ IsPSL 2 p 2 Q) ∨ IsSporadic .J1 Q) → False

end CFSG.Quasithin.Vol2.Ch10
