module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def KU3CensusHyp {X : Type} [Group X] (K D₀ : Subgroup X) (n p : ℕ) : Prop :=
  ⁅K, K⁆ = K ∧ IsL2 (Bar2 K) (2 * n) ∧ 2 ≤ n ∧ Even n ∧ p.Prime ∧ p ∣ 2 ^ n + 1 ∧ D₀ ≤ K ∧
    Nat.card D₀ = p ∧ centralizer (D₀ : Set X) ≤ normalizer (K : Set X) ∧ K ≠ ⊤

@[expose] def KU3CensusOdd : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (r f : ℕ), r ≠ 2 →
    (LieModel X .PSL 2 r f ∨ (r ^ f % 3 = 2 ∧ LieModel X .PSL 3 r f) ∨
      (r ^ f % 3 = 1 ∧ LieModel X .PSU 3 r f)) →
    ∀ K : Subgroup X, ⁅K, K⁆ = K → ∀ m : ℕ, 4 ≤ m → ¬ IsL2 (Bar2 K) m

@[expose] def KU3CensusL2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (f : ℕ), LieModel X .PSL 2 2 f →
    ∀ (K D₀ : Subgroup X) (n p : ℕ), ¬ KU3CensusHyp K D₀ n p

@[expose] def KU3CensusU3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (f : ℕ), Even f → LieModel X .PSU 3 2 f →
    ∀ (K D₀ : Subgroup X) (n p : ℕ), KU3CensusHyp K D₀ n p → f = 2 * n

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
