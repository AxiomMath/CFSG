module

public import CFSG.Quasithin.Background.F6SQTK
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup

variable {X : Type} [Group X]

@[expose] def StarCentralizes (A : Subgroup X) (r : ℕ) : Prop :=
  ∀ s : ℕ, s.Prime → s ≠ 2 → s ≠ r → ¬ r ∣ s ^ 2 - 1 → ∀ P : Subgroup X, IsPGroup s P →
    A ≤ normalizer (P : Set X) → A ≤ centralizer (P : Set X)

@[expose] def BarOne (A U : Subgroup X) : Prop :=
  IsSimpleGroup X ∧ U ⊔ normalizer (A : Set X) = ⊤ ∧
    ∃ Q : Subgroup X, IsPGroup 2 Q ∧ A ≤ normalizer (Q : Set X) ∧ ⁅Q, A⁆ ≠ ⊥

@[expose] def BarTwo (A : Subgroup X) : Prop :=
  IsSimpleGroup X ∧
    ((∃ p e : ℕ, p.Prime ∧ p ≠ 2 ∧ 5 < p ^ e ∧ CFSG.Quasithin.F6.IsL2 p e X) ∨
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧
        (CFSG.Blueprint.LieModel X .PSL 3 p f ∨ CFSG.Blueprint.LieModel X .PSU 3 p f)) ∧
    ∀ Q : Subgroup X, IsPGroup 2 Q → A ≤ normalizer (Q : Set X) → ⁅Q, A⁆ = ⊥

@[expose] def BarThree (A U : Subgroup X) (r : ℕ) : Prop :=
  ∃ L : Subgroup X, IsSimpleGroup L ∧ ⁅L, L⁆ = L ∧ A ≤ normalizer (L : Set X) ∧
    ⁅L, A⁆ ≠ ⊥ ∧ ¬ r ∣ Nat.card L ∧ (U ⊓ L) ⊔ (centralizer (A : Set X) ⊓ L) = L

@[expose] def K_UC146N_Bar : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (A U : Subgroup X) (r : ℕ),
    CFSG.Open.IsKGroup X → CFSG.solvableRadical X = ⊥ →
    r.Prime → 3 < r → (∃ n : ℕ, Odd n ∧ r ∣ 2 ^ n + 1) →
    Nat.card A = r → CFSG.ABGLocalTools.IsSylowOf 2 U ⊤ → UC22.Permutes A U →
    normalClosure (A : Set X) = ⊤ →
    CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 1 → CFSG.Open.pRank r (⊤ : Subgroup X) ≤ 1 →
    StarCentralizes A r →
    BarOne A U ∨ BarTwo A ∨ BarThree A U r

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
