module

public import CFSG.Open.SignalizerFunctorDefs
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Defs

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride

variable {G : Type*} [Group G]

structure IsFunctor (p : ℕ) (A : Subgroup G) (θ : G → Subgroup G) : Prop where
  le_centralizer : ∀ a ∈ A, a ≠ 1 → θ a ≤ Subgroup.centralizer {a}
  coprime : ∀ a ∈ A, a ≠ 1 → Nat.Coprime p (Nat.card (θ a))
  normalized : ∀ a ∈ A, a ≠ 1 → A ≤ Subgroup.normalizer (θ a : Set G)
  balance : ∀ a ∈ A, a ≠ 1 → ∀ b ∈ A, b ≠ 1 → θ a ⊓ Subgroup.centralizer {b} ≤ θ b

@[expose] def thetaOf (θ : G → Subgroup G) (B : Subgroup G) : Subgroup G :=
  ⨅ (b : G) (_ : b ∈ B) (_ : b ≠ 1), θ b

@[expose] def signalizers (p : ℕ) (A : Subgroup G) (θ : G → Subgroup G)
    (P : Subgroup G → Prop) : Set (Subgroup G) :=
  {X | A ≤ Subgroup.normalizer (X : Set G) ∧ Nat.Coprime p (Nat.card X) ∧
    (∀ a ∈ A, a ≠ 1 → X ⊓ Subgroup.centralizer {a} ≤ θ a) ∧ P X}

@[expose] def IsCompleteIn (S : Set (Subgroup G)) : Prop :=
  ∃ W ∈ S, ∀ X ∈ S, X ≤ W

@[expose] def IsLocallyCompleteIn (S : Set (Subgroup G)) : Prop :=
  ∀ X ∈ S, X ≠ ⊥ → ∃ Y ∈ S, Y ≤ Subgroup.normalizer (X : Set G) ∧
    ∀ Z ∈ S, Z ≤ Subgroup.normalizer (X : Set G) → Z ≤ Y

@[expose] def NearASolvable (p : ℕ) (A X : Subgroup G) : Prop :=
  signalizerNearPSolvable p X ∧
    Group.IsSolvable (X ⊓ Subgroup.centralizer (A : Set G) : Subgroup G)

@[expose] noncomputable def size (A : Subgroup G) (θ : G → Subgroup G) : ℕ :=
  ∑ᶠ (a : G) (_ : a ∈ A) (_ : a ≠ 1), Nat.card (θ a)

@[expose] def sol (X : Subgroup G) : Subgroup G :=
  (CFSG.solvableRadical X).map X.subtype

@[expose] def kOf (X : Subgroup G) : Subgroup G :=
  (CFSG.SignalizerFunctorTheorem.Nonsolvable.oStar X).map X.subtype

end CFSG.SignalizerFunctorTheorem.McBride
