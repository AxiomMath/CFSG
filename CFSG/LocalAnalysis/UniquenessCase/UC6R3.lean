module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] def R6_9 (D : Data G) : Prop :=
  D.sig ⊆ D.sig1 → ∀ r : ℕ, r.Prime → r ≠ 2 → ∀ E : Subgroup G, E ≤ D.M →
    CFSG.Open.IsElemAbelian r E → Nat.card E = r ^ 2 → rankThreeGamma 1 r E ≤ D.M →
    ∀ (p : ℕ) (X : Subgroup G), p.Prime → X ≤ D.M → Nat.card X = p →
      E ≤ normalizer (X : Set G) → ¬ normalizer (X : Set G) ≤ D.M →
      ∀ P : Subgroup G, P ≤ D.M → IsPGroup p P → X ≤ P →
        (Nat.card (CFSG.Open.pCoreOf 2 D.M ⊓ centralizer (X : Set G) : Subgroup G) ≤ 2 ∧
          (3 < r → CFSG.Open.pCoreOf 2 D.M ⊓ centralizer (X : Set G) = ⊥)) ∧
        (∀ y ∈ (Subgroup.upperCentralSeries ↥P 2).map P.subtype, ∀ x ∈ X, x * y = y * x) ∧
        (X ≤ (Subgroup.upperCentralSeries ↥P 2).map P.subtype → X ≤ (center ↥P).map P.subtype)

end CFSG.LocalAnalysis.UniquenessCase.UC6
