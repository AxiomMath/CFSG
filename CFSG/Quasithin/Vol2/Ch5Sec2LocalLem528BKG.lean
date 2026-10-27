module

public import CFSG.Quasithin.Background.A3Structure312Defs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def FactExcParabolicO2Ne : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L P : Subgroup G) (m : ℕ), 2 ≤ m →
    ((∃ f : ℕ, (2 ≤ f ∧ IsG2 2 f ↥L) ∨ (1 ≤ f ∧ Is3D4 2 f ↥L) ∨
        (Odd f ∧ 3 ≤ f ∧ Is2F4 f ↥L)) ∨ IsTits ↥L) →
    IsMaxParabolic2 L P → IsPSL 2 2 m (ModO2 (perfectCore P)) →
      CFSG.pCore 2 ↥(perfectCore P) ≠ ⊥

@[expose] def HatA7Faithful6 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsHat X (alternatingGroup (Fin 7)) →
    ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) → Nat.card V ≤ 2 ^ 6 →
      ∀ φ : X →* MulAut V, ¬ Function.Injective φ

@[expose] def A7Q528Fact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X Q K : Subgroup G),
    Q ≤ X → X ≤ Subgroup.normalizer (Q : Set G) →
    (∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) → (∀ a ∈ Q, a ^ 2 = 1) →
    X ⊓ Subgroup.centralizer (Q : Set G) ≤ Q → Nat.card Q ≤ 2 ^ 6 →
    (∃ α : ↥X →* alternatingGroup (Fin 7), Function.Surjective α ∧ α.ker = Q.subgroupOf X) →
    Q ≤ K → K ≤ X → ⁅Q, K⁆ = Q → ¬ 7 ∣ Q.relIndex K →
      Nat.card Q = 2 ^ 4 ∧
        ∀ W : Subgroup G, W ≤ Q → X ≤ Subgroup.normalizer (W : Set G) → W = ⊥ ∨ W = Q

end CFSG.Quasithin.H13
