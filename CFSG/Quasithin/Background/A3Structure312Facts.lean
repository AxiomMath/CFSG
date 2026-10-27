module

public import CFSG.Quasithin.Background.A3Structure312Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.SectionRank CFSG.Assembly.LowTwoRank

@[expose] def A312ListFacts : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → SQTKGroup X → CFSG.pCore 2 X = ⊥ →
    ∀ T : Subgroup X, CFSG.QuasithinUnique.IsSylowTwoOf T ⊤ → ∀ B ∈ lFamily T, B ≠ ⊤ →
      A312Case B ⊤

@[expose] def A312SL2Fact : Prop :=
  ∀ p : ℕ, p.Prime → 3 < p → ∀ (X : Type) [Group X] [Finite X], IsSL2 p X →
    ∀ S : Subgroup X, CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ → ∀ B ∈ lFamily S, B ≠ ⊤ →
      IsSL2 5 ↥B ∧ p ^ 2 % 5 = 1 ∧ (p % 8 = 3 ∨ p % 8 = 5)

structure A312Facts : Prop where
  list : A312ListFacts
  sl2 : A312SL2Fact

end CFSG.Quasithin
