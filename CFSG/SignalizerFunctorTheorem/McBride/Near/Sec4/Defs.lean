module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Defs

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

@[expose] noncomputable def permDeg (H : Type*) [Group H] : ℕ :=
  sInf {n : ℕ | ∃ f : H →* Equiv.Perm (Fin n), Function.Injective f}

@[expose] noncomputable def deg (H : Type*) [Group H] : ℕ :=
  permDeg (H ⧸ CFSG.solvableRadical H)

variable {H : Type*} [Group H]

@[expose] def bSet (H : Type*) [Group H] : Set (Subgroup H) :=
  {X | kOf X = X}

@[expose] def bOne (T : Set (Subgroup H)) : Set (Subgroup H) :=
  {X | X ∈ T ∧ ∀ Y ∈ T, deg Y ≤ deg X}

@[expose] def bTwo (T : Set (Subgroup H)) : Set (Subgroup H) :=
  {X | X ∈ bOne T ∧ ∀ Y ∈ bOne T,
    Nat.card (Y ⧸ CFSG.solvableRadical Y) ≤ Nat.card (X ⧸ CFSG.solvableRadical X)}

@[expose] def bStar (T : Set (Subgroup H)) : Set (Subgroup H) :=
  {X | X ∈ bTwo T ∧ ∀ Y ∈ bTwo T, Nat.card Y ≤ Nat.card X}

@[expose] def bTheta {G : Type*} [Group G] (p : ℕ) (A : Subgroup G) (θ : G → Subgroup G) :
    Set (Subgroup G) :=
  {Y | ∃ X ∈ mhat p A θ, Y ≤ X ∧ kOf Y = Y}

@[expose] def bStarTheta {G : Type*} [Group G] (p : ℕ) (A : Subgroup G) (θ : G → Subgroup G) :
    Set (Subgroup G) :=
  bStar (bTheta p A θ)

@[expose] def HypB (H : Type*) [Group H] : Prop :=
  IsSimpleGroup H ∧ (∃ a b : H, a * b ≠ b * a) ∧
    ∀ X ∈ bSet (MulAut H), Group.IsPerfect X → ¬ X ≤ (MulAut.conj : H →* MulAut H).range →
      deg X < deg H

@[expose] def HypC (H : Type*) [Group H] : Prop :=
  ∀ (K L : Subgroup H), L ≤ K → ∀ [(L.subgroupOf K).Normal],
    IsSimpleGroup (K ⧸ L.subgroupOf K) →
    (∃ a b : K ⧸ L.subgroupOf K, a * b ≠ b * a) →
    HypB (K ⧸ L.subgroupOf K)

end CFSG.SignalizerFunctorTheorem.McBride.Near
