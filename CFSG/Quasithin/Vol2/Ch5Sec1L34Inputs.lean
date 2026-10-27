module

public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def L34ElemNineFact : Prop :=
  ∀ (X : Type) [Group X], LieModel X .PSL 3 2 2 →
    ∃ E : Subgroup X, Nat.card E = 9 ∧ (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ ∀ a ∈ E, a ^ 3 = 1

@[expose] def SimpleThreePrimeSuzukiFact : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → CFSG.Quasithin.A23List S →
    ¬ 3 ∣ Nat.card S → ∃ k : ℕ, SuzukiModel S 2 k

@[expose] def SzTwoAutInnerFact : Prop :=
  ∀ (X : Type) [Group X] (k : ℕ), SuzukiModel X 2 k → ∀ α : MulAut X,
    (∃ m : ℕ, α ^ 2 ^ m = 1) → ∃ q : X, α = MulAut.conj q

@[expose] def L2PerfectThreePrimeFact : Prop :=
  ∀ (X : Type) [Group X] (n : ℕ), LieModel X .PSL 2 2 n →
    ∀ (Y : Type) [Group Y] [Finite Y] (φ : Y →* MulAut X), commutator Y = ⊤ →
      ¬ 3 ∣ Nat.card Y → φ = 1

end CFSG.Quasithin.H13
