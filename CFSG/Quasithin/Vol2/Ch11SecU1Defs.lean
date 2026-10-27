module

public import CFSG.Quasithin.Vol2.Ch11SecE3L0

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G]

@[expose] def OddTorus (L : Subgroup G) (b : G) : Prop :=
  ∃ P : Subgroup G, P ≤ L ⊓ Subgroup.centralizer {b} ∧ (Nat.card P).Prime ∧
    Nat.card P ≠ 2 ∧ Subgroup.centralizer {b} ≤ Subgroup.normalizer (P : Set G) ∧
    ∀ y ∈ L ⊓ Subgroup.centralizer {b}, orderOf y = 2 → y ≠ b → ¬ P ≤ Subgroup.centralizer {y}

@[expose] def SigmaFacts (L : Subgroup G) (b : G) : Prop :=
  ∃ L₀ : Subgroup G, L₀ ≤ L ⊓ Subgroup.centralizer {b} ∧ IsSimpleGroup ↥L₀ ∧
    (∃ x y : ↥L₀, x * y ≠ y * x) ∧ Subgroup.centralizer {b} ≤ Subgroup.normalizer (L₀ : Set G) ∧
    L ⊓ Subgroup.centralizer (L₀ : Set G) = ⊥

structure Setting [Finite G] (L : Subgroup G) : Prop where
  almostSimple : SecE3.AlmostSimple L
  two_dvd : 2 ∣ Nat.card L
  inner_conj : ∀ x ∈ L, ∀ y ∈ L, orderOf x = 2 → orderOf y = 2 → ∃ g ∈ L, g * x * g⁻¹ = y
  inner_solvable : ∀ x ∈ L, orderOf x = 2 → Group.IsSolvable ↥(L ⊓ Subgroup.centralizer {x})
  inner_max : ∀ x ∈ L, orderOf x = 2 → ∀ H : Subgroup G, L ⊓ Subgroup.centralizer {x} < H →
    H ≤ L → H = L
  inner_center : ∀ x ∈ L, orderOf x = 2 → ∀ y ∈ L ⊓ Subgroup.centralizer {x},
    (∀ w ∈ L ⊓ Subgroup.centralizer {x}, y * w = w * y) → y ∈ Subgroup.zpowers x
  inner_torus : ∀ x ∈ L, orderOf x = 2 → OddTorus L x
  outer : ∀ b : G, b ∉ L → orderOf b = 2 → OddTorus L b ∨ SigmaFacts L b
  outer_pair : ∀ t₁ t₂ : G, t₁ ∉ L → t₂ ∉ L → orderOf t₁ = 2 → orderOf t₂ = 2 →
    t₁ * t₂ = t₂ * t₁ → t₁ * t₂ ∈ L

@[expose] def TorusMember : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T A P : Subgroup G), IsSylowIn 2 T ⊤ → A ≤ T →
    IsElemAbelian 2 A → (Nat.card P).Prime → Nat.card P ≠ 2 →
    E1.tauOf ⊤ T A ≤ Subgroup.normalizer (P : Set G) →
    (∃ a ∈ A, ¬ P ≤ Subgroup.centralizer {a}) → E1.IsE 1 ⊤ T A (P ⊔ E1.tauOf ⊤ T A)

@[expose] def ComponentMember : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T A L₀ : Subgroup G), IsSylowIn 2 T ⊤ → A ≤ T →
    IsElemAbelian 2 A → IsSimpleGroup ↥L₀ → (∃ x y : ↥L₀, x * y ≠ y * x) →
    E1.tauOf ⊤ T A ≤ Subgroup.normalizer (L₀ : Set G) → IsSylowIn 2 (T ⊓ L₀) L₀ →
    (A ⊓ Subgroup.centralizer (L₀ : Set G)).relIndex A = 2 →
    E1.IsE 1 ⊤ T A (L₀ ⊔ E1.tauOf ⊤ T A)

end CFSG.Quasithin.Vol2.Ch11.SecU1
