module

public import CFSG.Open.Defs
public import CFSG.Open.GeneratedCore

public section

namespace CFSG.Open
open scoped MatrixGroups

variable {G : Type*} [Group G]

@[expose] noncomputable def uniqueThreeTwoLocalRank (p : ℕ) (G : Type*) [Group G] [Finite G] : ℕ :=
  twoLocalPrimeRank p G

open Classical in
@[expose] noncomputable def uniqueThreeSigmaA (G : Type*) [Group G] [Finite G] : Set ℕ :=
  let S₁ := {p | p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card G ∧ 3 < uniqueThreeTwoLocalRank p G}
  let S₂ := {p | p.Prime ∧ 5 < p ∧ p ∣ Nat.card G ∧ uniqueThreeTwoLocalRank p G = 3}
  let S₃ := {p | p.Prime ∧ 3 < p ∧ p ∣ Nat.card G ∧ uniqueThreeTwoLocalRank p G = 3}
  let S₄ := {p | p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card G ∧ uniqueThreeTwoLocalRank p G = 3}
  if S₁.Nonempty then S₁ else if S₂.Nonempty then S₂ else if S₃.Nonempty then S₃ else S₄

@[expose] def uniqueThreeIsMaxTwoLocal (M : Subgroup G) : Prop :=
  IsMaxTwoLocalSubgroup M

@[expose] noncomputable def uniqueThreeGamma [Finite G] (k p : ℕ) (R : Subgroup G) : Subgroup G :=
  GLBCore p k R

@[expose] def uniqueThreePrimeCore (p : ℕ) (H : Subgroup G) : Subgroup G :=
  relPPrimeCore p H

@[expose] def uniqueThreeLayer (H : Subgroup G) : Subgroup G :=
  sSup {L | IsComponentOf L H}

@[expose] def uniqueThreeConj (g : G) (H : Subgroup G) : Subgroup G :=
  H.map (MulAut.conj g⁻¹).toMonoidHom

@[expose] def uniqueThreeFrobeniusProduct (W K V : Subgroup G) : Prop :=
  ∃ X : Subgroup G, (∀ x, x ∈ X ↔ ∃ a ∈ W, ∃ b ∈ V, x = a * b) ∧
    (∀ x, x ∈ X ↔ ∃ a ∈ K, ∃ b ∈ V, x = a * b) ∧
    K ≠ ⊥ ∧ V ≠ ⊥ ∧ K ≤ X ∧ (K.subgroupOf X).Normal ∧ K ⊓ V = ⊥ ∧
    ∀ v ∈ V, v ≠ 1 → ∀ k ∈ K, k * v = v * k → k = 1

@[expose] def uniqueThreeIsQ8CentralCyclic (H : Subgroup G) (m : ℕ) : Prop :=
  ∃ A B : Subgroup G, Nonempty (A ≃* QuaternionGroup 2) ∧ IsCyclic B ∧ Nat.card B = 2 ^ m ∧
    (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) ∧ A ⊔ B = H ∧ Nat.card (A ⊓ B : Subgroup G) = 2

@[expose] def uniqueThreeClauseB [Finite G] (M P : Subgroup G) (p : ℕ) : Prop :=
  5 ≤ p ∧ Group.IsSolvable M ∧
    ∃ P₀ : Subgroup G, P₀ ≤ P ∧ Nat.card P₀ = p ∧
      (∀ g : G, uniqueThreeConj g P₀ ≤ P → uniqueThreeConj g P₀ = P₀) ∧
      (∃ (_ : Fact p.Prime) (m : ℕ), 2 ≤ m ∧
        Nonempty (uniqueThreeLayer (Subgroup.centralizer (P₀ : Set G)) ≃*
          PSL(2, GaloisField p m))) ∧
      ¬ uniqueThreeLayer (Subgroup.centralizer (P₀ : Set G)) ≤ M ∧
      uniqueThreeFrobeniusProduct (uniqueThreePrimeCore p M) (pCoreOf 2 M)
        (Subgroup.centralizer (uniqueThreeLayer (Subgroup.centralizer (P₀ : Set G)) : Set G)) ∧
      ∀ Y : Subgroup G, Y ≤ P → Nat.card Y = p → Y ≠ P₀ →
        Subgroup.normalizer (Y : Set G) ≤ M

@[expose] def uniqueThreeClauseC [Finite G] (M P : Subgroup G) : Prop :=
  Group.IsSolvable M ∧
    Nonempty (P ≃* (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3))) ∧
    uniqueThreeGamma 1 3 (thompsonSubgroup P) ≤ M ∧
    ∀ Y : Subgroup G, Y ≤ P → Nat.card Y = 3 → ¬ Y ≤ thompsonSubgroup P →
      ∃ Q : Subgroup G, Q ≤ uniqueThreePrimeCore 3 M ∧ IsPGroup 2 Q ∧
        ¬ 2 ∣ (Q.subgroupOf (uniqueThreePrimeCore 3 M)).index ∧
        P ≤ Subgroup.normalizer (Q : Set G) ∧
        ∃ m : ℕ, 1 ≤ m ∧
          uniqueThreeIsQ8CentralCyclic (Q ⊓ Subgroup.centralizer (Y : Set G)) m

@[expose] def uniqueThreeUC (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ p ∈ uniqueThreeSigmaA G, ∃ (P : Sylow p G) (M : Subgroup G),
    uniqueThreeIsMaxTwoLocal M ∧
    uniqueThreeGamma 2 p P ≤ M ∧
    (uniqueThreeGamma 1 p P ≤ M ∨ uniqueThreeClauseB M P p ∨
      (p = 3 ∧ uniqueThreeClauseC M P)) ∧
    ∀ H : Subgroup G, IsTwoLocal H → 2 ≤ pRank p (H ⊓ M) → H ≤ M

end CFSG.Open
