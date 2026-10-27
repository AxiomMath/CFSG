module

public import Mathlib
public import CFSG.GroupTheory.PCore.Construction

public section

namespace CFSG.Open

export CFSG (pCore)

@[expose] def IsElemAbelian (p : ℕ) {G : Type*} [Group G] (E : Subgroup G) : Prop :=
  IsMulCommutative E ∧ ∀ x ∈ E, x ^ p = 1

@[expose] noncomputable def pRank (p : ℕ) {G : Type*} [Group G] [Finite G] (H : Subgroup G) : ℕ :=
  sSup {k | ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian p E ∧ Nat.card E = p ^ k}

@[expose] noncomputable def twoRank (G : Type*) [Group G] [Finite G] : ℕ := pRank 2 (⊤ : Subgroup G)

@[expose] def IsTwoLocal {G : Type*} [Group G] (H : Subgroup G) : Prop :=
  ∃ P : Subgroup G, P ≠ ⊥ ∧ IsPGroup 2 P ∧ H = Subgroup.normalizer (P : Set G)

@[expose] def IsMaxTwoLocalSubgroup {G : Type*} [Group G] (M : Subgroup G) : Prop :=
  IsTwoLocal M ∧ ∀ H : Subgroup G, IsTwoLocal H → M ≤ H → H = M

@[expose] def pCoreOf (p : ℕ) {G : Type*} [Group G] (H : Subgroup G) : Subgroup G :=
  (pCore p H).map H.subtype

@[expose] def relPPrimeCore (p : ℕ) {G : Type*} [Group G] (H : Subgroup G) : Subgroup G :=
  sSup {N | N ≤ H ∧ (N.subgroupOf H).Normal ∧ Nat.Coprime p (Nat.card N)}

@[expose] def IsCharTwoType (G : Type*) [Group G] : Prop :=
  ∀ H : Subgroup G, IsTwoLocal H →
    H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ≤ pCoreOf 2 H

@[expose] noncomputable def evenRank (G : Type*) [Group G] [Finite G] : ℕ :=
  sSup {k | ∃ (p : ℕ) (H : Subgroup G), p.Prime ∧ p ≠ 2 ∧ IsTwoLocal H ∧ pRank p H = k}

@[expose] noncomputable def twoLocalPrimeRank (p : ℕ) (G : Type*) [Group G] [Finite G] : ℕ :=
  sSup {k | ∃ H : Subgroup G, IsTwoLocal H ∧ pRank p H = k}

end CFSG.Open
