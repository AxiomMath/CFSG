module

public import CFSG.Monster.GMS.Facts.LeechType

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

@[expose] def Co1TwoBFacts : Prop :=
  ∀ s : Co1, IsCo1TwoB s →
    Nat.card ↥(Subgroup.centralizer ({s} : Set Co1)) ≤ 2 ^ 15 * 3 ^ 3 * 5 ^ 2 * 7 * 13 ∧
    (∀ v ∈ co1Fix s, v ≠ 0 → v ∈ co1Orbit 2) ∧
    (∀ v ∈ co1Fix s, ∀ w ∈ co1Fix s, v ≠ 0 → w ≠ 0 →
      ∃ g ∈ Subgroup.centralizer ({s} : Set Co1), co1Act g v = w) ∧
    ∀ H : Subgroup Co1, H ≤ Subgroup.centralizer ({s} : Set Co1) →
      Nat.card ↥(Subgroup.centralizer ({s} : Set Co1)) ≤ 2 * Nat.card H →
      ∀ N : Subgroup Co1, N ≤ H → (∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) → IsPGroup 2 N →
        Nat.card N ≤ 2 ^ 11

end CFSG.Monster.GMS
