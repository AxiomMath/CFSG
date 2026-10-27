module

public import CFSG.RankThree.PartOne.S12.Skeleton
public import CFSG.RankThree.PartOne.S12.InputsLinear
public import CFSG.RankThree.PartOne.S12.InputsTable

public section

namespace CFSG.RankThree.PartOne

@[expose] def LAFaithful (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    (Γ : Subgroup (V ≃ₗ[ZMod p] V)) (B : Submodule (ZMod p) V),
    Module.finrank (ZMod p) B + 1 = Module.finrank (ZMod p) V →
    (∀ g ∈ Γ, ∀ b ∈ B, g b ∈ B) → CFSG.pCore p Γ = ⊥ →
    (¬ ∃ ℓ : Submodule (ZMod p) V, Module.finrank (ZMod p) ℓ = 1 ∧ Disjoint ℓ B ∧
      ∀ g ∈ Γ, ∀ x ∈ ℓ, g x ∈ ℓ) →
    ∀ g ∈ Γ, (∀ b ∈ B, g b = b) → g = 1

@[expose] def LA126 : Prop :=
  ExtDickson → ExtBloomPrime → ExtJonesParshall → KF126 →
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    [Module.Finite (ZMod p) V] (Γ : Subgroup (V ≃ₗ[ZMod p] V)) (B : Submodule (ZMod p) V),
    Module.finrank (ZMod p) B + 1 = Module.finrank (ZMod p) V →
    (Module.finrank (ZMod p) B = 2 ∨ Module.finrank (ZMod p) B = 3) →
    (∀ g ∈ Γ, ∀ b ∈ B, g b ∈ B) → CFSG.pCore p Γ = ⊥ →
    (∀ g ∈ Γ, (∀ b ∈ B, g b = b) → g = 1) →
    (∀ B' ≤ B, (∀ g ∈ Γ, ∀ b ∈ B', g b ∈ B') → B' = ⊥ ∨ B' = B) →
    (¬ ∃ ℓ : Submodule (ZMod p) V, Module.finrank (ZMod p) ℓ = 1 ∧ Disjoint ℓ B ∧
      ∀ g ∈ Γ, ∀ x ∈ ℓ, g x ∈ ℓ) →
    p = 5 ∧ Module.finrank (ZMod p) B = 3 ∧
      ∃ Y : Subgroup (V ≃ₗ[ZMod p] V), Y ≤ Γ ∧ (∀ g ∈ Γ, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y) ∧
        Nat.card Y = 60 ∧
        (∀ Λ : Subgroup (V ≃ₗ[ZMod p] V), Λ ≤ Γ → Group.IsPerfect Λ → Λ ≤ Y) ∧
        Group.IsPerfect Y ∧ Nonempty (Y ≃* alternatingGroup (Fin 5)) ∧
        ∀ g ∈ Γ, (∀ y ∈ Y, g * y = y * g) → ∃ c : ZMod p, ∀ b ∈ B, g b = c • b

@[expose] def Node126g : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → ¬ torusIrreducible E → ¬ torusWeylHasPCore p E →
      p = 5 ∧ RowModel p L 9 ∧ Nat.card E = p ^ 4 ∧ E ≠ A

@[expose] def Node126k : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → ¬ torusIrreducible E → ¬ torusWeylHasPCore p E →
      p = 5 → RowModel p L 9 → Nat.card E = p ^ 4 → E ≠ A →
      Outcome152Five p E A (lieGenerated p E)

theorem node126_of_parts (hg : Node126g) (hk : Node126k) : Node126 := by
  intro G _ _ p A c L E h
  by_cases hirr : torusIrreducible E
  · exact Or.inl hirr
  by_cases hcore : torusWeylHasPCore p E
  · exact Or.inr (Or.inl hcore)
  obtain ⟨h5, h9, hE4, hEA⟩ := hg G p A c L E h hirr hcore
  exact Or.inr (Or.inr (hk G p A c L E h hirr hcore h5 h9 hE4 hEA))

end CFSG.RankThree.PartOne
