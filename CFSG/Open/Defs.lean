module

public import Mathlib
public import CFSG.Open.Catalog
public import CFSG.Foundations.KCore
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Classification

public section

namespace CFSG.Open

@[expose] def ordA (n q : ℕ) : ℕ :=
  q ^ (n * (n + 1) / 2) * (∏ i ∈ Finset.Icc 2 (n + 1), (q ^ i - 1)) / Nat.gcd (n + 1) (q - 1)

@[expose] def ordTwistedA (n q : ℕ) : ℕ :=
  q ^ (n * (n + 1) / 2) * (∏ i ∈ Finset.Icc 2 (n + 1), (q ^ i - (-1 : ℤ) ^ i).toNat) /
    Nat.gcd (n + 1) (q + 1)

@[expose] def ordBC (n q : ℕ) : ℕ :=
  q ^ (n * n) * (∏ i ∈ Finset.Icc 1 n, (q ^ (2 * i) - 1)) / Nat.gcd 2 (q - 1)

@[expose] def ordD (n q : ℕ) : ℕ :=
  q ^ (n * (n - 1)) * (q ^ n - 1) * (∏ i ∈ Finset.Icc 1 (n - 1), (q ^ (2 * i) - 1)) /
    Nat.gcd 4 (q ^ n - 1)

@[expose] def ordTwistedD (n q : ℕ) : ℕ :=
  q ^ (n * (n - 1)) * (q ^ n + 1) * (∏ i ∈ Finset.Icc 1 (n - 1), (q ^ (2 * i) - 1)) /
    Nat.gcd 4 (q ^ n + 1)

@[expose] def ordE6 (q : ℕ) : ℕ :=
  q ^ 36 * (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 - 1) * (q ^ 2 - 1) /
    Nat.gcd 3 (q - 1)

@[expose] def ordTwistedE6 (q : ℕ) : ℕ :=
  q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) * (q ^ 2 - 1) /
    Nat.gcd 3 (q + 1)

@[expose] def ordE7 (q : ℕ) : ℕ :=
  q ^ 63 * (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) * (q ^ 8 - 1) *
    (q ^ 6 - 1) * (q ^ 2 - 1) / Nat.gcd 2 (q - 1)

@[expose] def ordE8 (q : ℕ) : ℕ :=
  q ^ 120 * (q ^ 30 - 1) * (q ^ 24 - 1) * (q ^ 20 - 1) * (q ^ 18 - 1) * (q ^ 14 - 1) *
    (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 2 - 1)

@[expose] def ordF4 (q : ℕ) : ℕ :=
  q ^ 24 * (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1)

@[expose] def ordG2 (q : ℕ) : ℕ := q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1)

@[expose] def ordTrialityD4 (q : ℕ) : ℕ :=
  q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1)

@[expose] def ordSuzuki (q : ℕ) : ℕ := q ^ 2 * (q ^ 2 + 1) * (q - 1)

@[expose] def ordRee (q : ℕ) : ℕ := q ^ 3 * (q ^ 3 + 1) * (q - 1)

@[expose] def ordTwistedF4 (q : ℕ) : ℕ :=
  q ^ 12 * (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1)

@[expose] def ordTits : ℕ := 2 ^ 11 * 3 ^ 3 * 5 ^ 2 * 13

@[expose] def sporadicOrderList : Finset ℕ :=
  { 2 ^ 4 * 3 ^ 2 * 5 * 11, 2 ^ 6 * 3 ^ 3 * 5 * 11, 2 ^ 7 * 3 ^ 2 * 5 * 7 * 11,
    2 ^ 7 * 3 ^ 2 * 5 * 7 * 11 * 23, 2 ^ 10 * 3 ^ 3 * 5 * 7 * 11 * 23, 2 ^ 3 * 3 * 5 * 7 * 11 * 19,
    2 ^ 7 * 3 ^ 3 * 5 ^ 2 * 7, 2 ^ 7 * 3 ^ 5 * 5 * 17 * 19,
    2 ^ 21 * 3 ^ 3 * 5 * 7 * 11 ^ 3 * 23 * 29 * 31 * 37 * 43, 2 ^ 9 * 3 ^ 2 * 5 ^ 3 * 7 * 11,
    2 ^ 7 * 3 ^ 6 * 5 ^ 3 * 7 * 11, 2 ^ 10 * 3 ^ 3 * 5 ^ 2 * 7 ^ 3 * 17,
    2 ^ 14 * 3 ^ 3 * 5 ^ 3 * 7 * 13 * 29, 2 ^ 13 * 3 ^ 7 * 5 ^ 2 * 7 * 11 * 13,
    2 ^ 9 * 3 ^ 4 * 5 * 7 ^ 3 * 11 * 19 * 31, 2 ^ 10 * 3 ^ 7 * 5 ^ 3 * 7 * 11 * 23,
    2 ^ 18 * 3 ^ 6 * 5 ^ 3 * 7 * 11 * 23, 2 ^ 21 * 3 ^ 9 * 5 ^ 4 * 7 ^ 2 * 11 * 13 * 23,
    2 ^ 17 * 3 ^ 9 * 5 ^ 2 * 7 * 11 * 13, 2 ^ 18 * 3 ^ 13 * 5 ^ 2 * 7 * 11 * 13 * 17 * 23,
    2 ^ 21 * 3 ^ 16 * 5 ^ 2 * 7 ^ 3 * 11 * 13 * 17 * 23 * 29, 2 ^ 14 * 3 ^ 6 * 5 ^ 6 * 7 * 11 * 19,
    2 ^ 8 * 3 ^ 7 * 5 ^ 6 * 7 * 11 * 31 * 37 * 67, 2 ^ 15 * 3 ^ 10 * 5 ^ 3 * 7 ^ 2 * 13 * 19 * 31,
    2 ^ 41 * 3 ^ 13 * 5 ^ 6 * 7 ^ 2 * 11 * 13 * 17 * 19 * 23 * 31 * 47,
    2 ^ 46 * 3 ^ 20 * 5 ^ 9 * 7 ^ 6 * 11 ^ 2 * 13 ^ 3 * 17 * 19 * 23 * 29 * 31 * 41 * 47 * 59 *
      71 }

@[expose] def lieOrdersOver (q : ℕ) : Set ℕ :=
  {m | ∃ n, 1 ≤ n ∧ m = ordA n q} ∪ {m | ∃ n, 2 ≤ n ∧ m = ordTwistedA n q} ∪
  {m | ∃ n, 2 ≤ n ∧ m = ordBC n q} ∪ {m | ∃ n, 4 ≤ n ∧ m = ordD n q} ∪
  {m | ∃ n, 4 ≤ n ∧ m = ordTwistedD n q} ∪
  {ordE6 q, ordTwistedE6 q, ordE7 q, ordE8 q, ordF4 q, ordG2 q, ordTrialityD4 q}

@[expose] def lieOrdersChar (p : ℕ) : Set ℕ :=
  {m | ∃ k, 1 ≤ k ∧ m ∈ lieOrdersOver (p ^ k)} ∪
  {m | p = 2 ∧ ∃ k, 1 ≤ k ∧ (m = ordSuzuki (2 ^ (2 * k + 1)) ∨
    m = ordTwistedF4 (2 ^ (2 * k + 1)))} ∪
  {m | p = 3 ∧ ∃ k, 1 ≤ k ∧ m = ordRee (3 ^ (2 * k + 1))} ∪
  {m | p = 2 ∧ m = ordTits}

@[expose] def knownSimpleOrders : Set ℕ :=
  {m | m.Prime} ∪ {m | ∃ n, 5 ≤ n ∧ m = Nat.factorial n / 2} ∪
  {m | ∃ p, p.Prime ∧ m ∈ lieOrdersChar p} ∪ (sporadicOrderList : Set ℕ)

@[expose] def IsCatalogGroup (H : Type*) [Group H] : Prop :=
  ∃ i : TauCeti.CFSGIndex, Nonempty (H ≃* i.Group)

@[expose] def IsKGroup (X : Type*) [Group X] : Prop :=
  KCore.KGroupNonab @IsCatalogGroup X

@[expose] def IsKProper (G : Type*) [Group G] : Prop :=
  KCore.KProperNonab @IsCatalogGroup G

@[expose] def IsQuasisimple (G : Type*) [Group G] : Prop :=
  commutator G = ⊤ ∧ IsSimpleGroup (G ⧸ Subgroup.center G)

inductive IsSubnormal {G : Type*} [Group G] : Subgroup G → Subgroup G → Prop
  | refl (H : Subgroup G) : IsSubnormal H H
  | step {H M K : Subgroup G} : H ≤ M → (H.subgroupOf M).Normal → IsSubnormal M K →
      IsSubnormal H K

@[expose] def IsComponentOf {G : Type*} [Group G] (L K : Subgroup G) : Prop :=
  L ≤ K ∧ IsSubnormal L K ∧ IsQuasisimple L

@[expose] def HasInvolutionComponent (G : Type*) [Group G] : Prop :=
  ∃ (t : G) (L : Subgroup G), t ≠ 1 ∧ t ^ 2 = 1 ∧
    IsComponentOf L (Subgroup.centralizer ({t} : Set G))

end CFSG.Open