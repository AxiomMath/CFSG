module

public import Mathlib
public import CFSG.Open.Defs

public section

namespace CFSG.Open

open Finset

@[expose] def orderA (n q : ℕ) : ℕ :=
  q ^ (n * (n + 1) / 2) * (∏ i ∈ Icc 2 (n + 1), (q ^ i - 1)) / Nat.gcd (n + 1) (q - 1)

@[expose] def orderTwistedA (n q : ℕ) : ℕ :=
  q ^ (n * (n + 1) / 2) * (∏ i ∈ Icc 2 (n + 1), if Even i then q ^ i - 1 else q ^ i + 1) /
    Nat.gcd (n + 1) (q + 1)

@[expose] def orderBC (n q : ℕ) : ℕ :=
  q ^ (n * n) * (∏ i ∈ Icc 1 n, (q ^ (2 * i) - 1)) / Nat.gcd 2 (q - 1)

@[expose] def orderD (n q : ℕ) : ℕ :=
  q ^ (n * (n - 1)) * (q ^ n - 1) * (∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1)) /
    Nat.gcd 4 (q ^ n - 1)

@[expose] def orderTwistedD (n q : ℕ) : ℕ :=
  q ^ (n * (n - 1)) * (q ^ n + 1) * (∏ i ∈ Icc 1 (n - 1), (q ^ (2 * i) - 1)) /
    Nat.gcd 4 (q ^ n + 1)

@[expose] def orderE6 (q : ℕ) : ℕ :=
  q ^ 36 * (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 - 1) * (q ^ 2 - 1) /
    Nat.gcd 3 (q - 1)

@[expose] def orderTwistedE6 (q : ℕ) : ℕ :=
  q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) * (q ^ 2 - 1) /
    Nat.gcd 3 (q + 1)

@[expose] def orderE7 (q : ℕ) : ℕ :=
  q ^ 63 * (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
    (q ^ 2 - 1) / Nat.gcd 2 (q - 1)

@[expose] def orderE8 (q : ℕ) : ℕ :=
  q ^ 120 * (q ^ 30 - 1) * (q ^ 24 - 1) * (q ^ 20 - 1) * (q ^ 18 - 1) * (q ^ 14 - 1) *
    (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 2 - 1)

@[expose] def orderF4 (q : ℕ) : ℕ :=
  q ^ 24 * (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1)

@[expose] def orderG2 (q : ℕ) : ℕ :=
  q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1)

@[expose] def orderTrialityD4 (q : ℕ) : ℕ :=
  q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1)

@[expose] def orderSuzuki (q : ℕ) : ℕ :=
  q ^ 2 * (q ^ 2 + 1) * (q - 1)

@[expose] def orderRee (q : ℕ) : ℕ :=
  q ^ 3 * (q ^ 3 + 1) * (q - 1)

@[expose] def orderTwistedF4 (q : ℕ) : ℕ :=
  q ^ 12 * (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1)

@[expose] def orderTits : ℕ := 2 ^ 11 * 3 ^ 3 * 5 ^ 2 * 13

@[expose] def sporadicOrders : Finset ℕ :=
  { 2 ^ 4 * 3 ^ 2 * 5 * 11,
    2 ^ 6 * 3 ^ 3 * 5 * 11,
    2 ^ 7 * 3 ^ 2 * 5 * 7 * 11,
    2 ^ 7 * 3 ^ 2 * 5 * 7 * 11 * 23,
    2 ^ 10 * 3 ^ 3 * 5 * 7 * 11 * 23,
    2 ^ 3 * 3 * 5 * 7 * 11 * 19,
    2 ^ 7 * 3 ^ 3 * 5 ^ 2 * 7,
    2 ^ 7 * 3 ^ 5 * 5 * 17 * 19,
    2 ^ 21 * 3 ^ 3 * 5 * 7 * 11 ^ 3 * 23 * 29 * 31 * 37 * 43,
    2 ^ 9 * 3 ^ 2 * 5 ^ 3 * 7 * 11,
    2 ^ 7 * 3 ^ 6 * 5 ^ 3 * 7 * 11,
    2 ^ 10 * 3 ^ 3 * 5 ^ 2 * 7 ^ 3 * 17,
    2 ^ 14 * 3 ^ 3 * 5 ^ 3 * 7 * 13 * 29,
    2 ^ 13 * 3 ^ 7 * 5 ^ 2 * 7 * 11 * 13,
    2 ^ 9 * 3 ^ 4 * 5 * 7 ^ 3 * 11 * 19 * 31,
    2 ^ 10 * 3 ^ 7 * 5 ^ 3 * 7 * 11 * 23,
    2 ^ 18 * 3 ^ 6 * 5 ^ 3 * 7 * 11 * 23,
    2 ^ 21 * 3 ^ 9 * 5 ^ 4 * 7 ^ 2 * 11 * 13 * 23,
    2 ^ 17 * 3 ^ 9 * 5 ^ 2 * 7 * 11 * 13,
    2 ^ 18 * 3 ^ 13 * 5 ^ 2 * 7 * 11 * 13 * 17 * 23,
    2 ^ 21 * 3 ^ 16 * 5 ^ 2 * 7 ^ 3 * 11 * 13 * 17 * 23 * 29,
    2 ^ 14 * 3 ^ 6 * 5 ^ 6 * 7 * 11 * 19,
    2 ^ 8 * 3 ^ 7 * 5 ^ 6 * 7 * 11 * 31 * 37 * 67,
    2 ^ 15 * 3 ^ 10 * 5 ^ 3 * 7 ^ 2 * 13 * 19 * 31,
    2 ^ 41 * 3 ^ 13 * 5 ^ 6 * 7 ^ 2 * 11 * 13 * 17 * 19 * 23 * 31 * 47,
    2 ^ 46 * 3 ^ 20 * 5 ^ 9 * 7 ^ 6 * 11 ^ 2 * 13 ^ 3 * 17 * 19 * 23 * 29 * 31 * 41 * 47 *
      59 * 71 }

@[expose] def cfsgOrders : Set ℕ :=
  {m | m.Prime} ∪
  {m | ∃ n : ℕ, 5 ≤ n ∧ m = Nat.factorial n / 2} ∪
  {m | ∃ n q : ℕ, 1 ≤ n ∧ IsPrimePow q ∧ m = orderA n q} ∪
  {m | ∃ n q : ℕ, 2 ≤ n ∧ IsPrimePow q ∧ m = orderTwistedA n q} ∪
  {m | ∃ n q : ℕ, 2 ≤ n ∧ IsPrimePow q ∧ m = orderBC n q} ∪
  {m | ∃ n q : ℕ, 4 ≤ n ∧ IsPrimePow q ∧ m = orderD n q} ∪
  {m | ∃ n q : ℕ, 4 ≤ n ∧ IsPrimePow q ∧ m = orderTwistedD n q} ∪
  {m | ∃ q : ℕ, IsPrimePow q ∧
    (m = orderE6 q ∨ m = orderTwistedE6 q ∨ m = orderE7 q ∨ m = orderE8 q ∨
      m = orderF4 q ∨ m = orderG2 q ∨ m = orderTrialityD4 q)} ∪
  {m | ∃ k : ℕ, 1 ≤ k ∧
    (m = orderSuzuki (2 ^ (2 * k + 1)) ∨ m = orderTwistedF4 (2 ^ (2 * k + 1)))} ∪
  {m | ∃ k : ℕ, 1 ≤ k ∧ m = orderRee (3 ^ (2 * k + 1))} ∪
  {orderTits} ∪
  (sporadicOrders : Set ℕ)

@[expose] def IsKProperByOrder (G : Type*) [Group G] : Prop :=
  ∀ (K L : Subgroup G), K ≠ ⊤ → L ≤ K → ∀ [(L.subgroupOf K).Normal],
    IsSimpleGroup (K ⧸ L.subgroupOf K) →
    (∃ a b : K ⧸ L.subgroupOf K, a * b ≠ b * a) →
    Nat.card (K ⧸ L.subgroupOf K) ∈ knownSimpleOrders

@[expose] def componentClassificationOddCore (H : Type*) [Group H] : Subgroup H :=
  sSup {N : Subgroup H | N.Normal ∧ Odd (Nat.card N)}

instance componentClassificationOddCore_normal (H : Type*) [Group H] :
    (componentClassificationOddCore H).Normal :=
  Subgroup.sSup_normal _ fun _ hN => hN.1

@[expose] def componentClassificationComponentType (G : Type*) [Group G] : Prop :=
  ∃ t : G, orderOf t = 2 ∧
    ∃ L : Subgroup (Subgroup.centralizer ({t} : Set G) ⧸
        componentClassificationOddCore (Subgroup.centralizer ({t} : Set G))),
      IsComponentOf L ⊤

@[expose] def disconnectedInvolutionCommutingGraph (G : Type*) [Group G] :
    SimpleGraph {t : G // orderOf t = 2} :=
  SimpleGraph.fromRel fun t u => (t : G) * u = u * t

end CFSG.Open
