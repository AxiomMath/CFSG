
module

public import CFSG.Monster.GMS.Facts.Co1Local
public import CFSG.Sporadic.Co1.Module.FormsBase

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

@[expose] def IsCo1TwoA (r : Co1) : Prop :=
  orderOf r = 2 ∧ (co1Fix r).ncard * Nat.card ↥(Subgroup.centralizer ({r} : Set Co1)) =
    2 ^ 37 * 3 ^ 5 * 5 ^ 2 * 7

@[expose] def Co1CommonFour (r s : Co1) : Prop :=
  ∃ v ∈ co1Orbit 2, v ∈ co1Fix r ∧ v ∈ co1Fix s

@[expose] def Co1OddType (r s : Co1) : Fin 3 → Prop
  | 0 => orderOf (r * s) = 3 ∧ (co1Fix r ∩ co1Fix s).ncard = 2 ^ 10 ∧
      Nat.card ↥(Subgroup.centralizer ({r} : Set Co1) ⊓ Subgroup.centralizer {s}) =
        2 ^ 7 * 3 ^ 5 * 5
  | 1 => orderOf (r * s) = 3 ∧ (co1Fix r ∩ co1Fix s).ncard = 2 ^ 8 ∧
      Nat.card ↥(Subgroup.centralizer ({r} : Set Co1) ⊓ Subgroup.centralizer {s}) =
        2 ^ 6 * 3 ^ 4 * 5 * 7
  | 2 => orderOf (r * s) = 5 ∧ (co1Fix r ∩ co1Fix s).ncard = 2 ^ 8 ∧
      Nat.card ↥(Subgroup.centralizer ({r} : Set Co1) ⊓ Subgroup.centralizer {s}) =
        2 ^ 5 * 3 ^ 2 * 5 ^ 2

@[expose] def Co1OddPairFacts : Prop :=
  ∀ r : Co1, IsCo1TwoA r →
    (∀ s, IsConj r s → s ≠ r → Odd (orderOf (r * s)) → Co1CommonFour r s →
      ∃! k, Co1OddType r s k) ∧
    (∀ k, ∃ s, IsConj r s ∧ s ≠ r ∧ Co1CommonFour r s ∧ Co1OddType r s k) ∧
    (∀ k s s', IsConj r s → IsConj r s' → Co1CommonFour r s → Co1CommonFour r s' →
      Co1OddType r s k → Co1OddType r s' k →
        ∃ g ∈ Subgroup.centralizer ({r} : Set Co1), g * s * g⁻¹ = s') ∧
    (∀ k s, k ≠ 0 → IsConj r s → Co1CommonFour r s → Co1OddType r s k →
      (∀ u ∈ co1Fix r ∩ co1Fix s, (∀ v ∈ co1Fix r ∩ co1Fix s,
          CFSG.Sporadic.Co1.Module.bil₀ u v = 0) → u = 0) ∧
      ∀ g ∈ Subgroup.centralizer ({r} : Set Co1) ⊓ Subgroup.centralizer {s},
        (∀ v ∈ co1Fix r ∩ co1Fix s, co1Act g v = v) → g = 1)

end CFSG.Monster.GMS
