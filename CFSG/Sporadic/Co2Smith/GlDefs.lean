module

public import CFSG.Sporadic.Co2Smith.CData
public import CFSG.Sporadic.Co2Rank3.FactsBase

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Rank3 CFSG.Sporadic.Co2Cert

@[expose] def smithX {G : Type*} [Group G] (G₁ : Subgroup G) (u v : G) : Set G :=
  {g | g ∈ G₁ ∨ (∃ a ∈ G₁, ∃ b ∈ G₁, g = a * u * b) ∨ ∃ a ∈ G₁, ∃ b ∈ G₁, g = a * v * b}

@[expose] def SmithGlobalHyps
    {G : Type*} [Group G] (z : G)
    (φ : centralizer ({z} : Set G) ≃* Cz) : Prop :=
  (∀ g : G, ∀ ht : g⁻¹ * z * g ∈ centralizer ({z} : Set G),
      (⟨_, ht⟩ : centralizer ({z} : Set G)) ∈ CFSG.pCore 2 (centralizer ({z} : Set G)) →
        g⁻¹ * z * g = z) ∧
    (∀ g : G, ∀ ht : g⁻¹ * z * g ∈ centralizer ({z} : Set G), g⁻¹ * z * g = z ∨
      ∃ i ∈ ({1, 2, 5} : Finset (Fin 9)), ∃ h : Cz, h * φ ⟨_, ht⟩ * h⁻¹ = cR i) ∧
    ∃ g : G, ∃ ht : g⁻¹ * z * g ∈ centralizer ({z} : Set G), ∃ h : Cz,
      h * φ ⟨_, ht⟩ * h⁻¹ = cR 5

@[expose] def SmithC0Marking {G : Type*} [Group G] {z : G}
    (φ : centralizer ({z} : Set G) ≃* Cz) {C0c : Subgroup K} (α3c : Cz) (ρ : C0c →* G) :
    Prop :=
  Function.Injective ρ ∧
    (∀ w : C0c, ρ w * (φ.symm α3c : G) = (φ.symm α3c : G) * ρ w) ∧
    ∀ (w : C0c) (hw : (w : K) ∈ Cz), ρ w = (φ.symm ⟨w, hw⟩ : G)

@[expose] def SmithC0Input
    (C0c : Subgroup K) (α3c : Cz) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G), IsSimpleGroup G → SmithHyp G z →
    ∀ φ : centralizer ({z} : Set G) ≃* Cz, SmithGlobalHyps z φ →
      ∃ ρ : C0c →* G, SmithC0Marking φ α3c ρ

@[expose] def SmithU62Input
    (C0c : Subgroup K)
    (α3c : Cz) (G1c : Subgroup K) (c : Equiv.Perm (Fin 2300)) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G), IsSimpleGroup G → SmithHyp G z →
    ∀ φ : centralizer ({z} : Set G) ≃* Cz, SmithGlobalHyps z φ →
      ∀ ρ : C0c →* G, SmithC0Marking φ α3c ρ →
        ∃ (G₁ : Subgroup G) (ψ : G₁ ≃* co2P0),
          (∀ (h : G₁) (hz : (h : G) ∈ centralizer ({z} : Set G)),
            (ψ h : Equiv.Perm (Fin 2300)) =
              c * (co2PermEquiv (φ ⟨h, hz⟩ : K) : Equiv.Perm (Fin 2300)) * c⁻¹) ∧
          ∀ w : C0c, (w : K) ∈ G1c → ∃ hw : ρ w ∈ G₁,
            (ψ ⟨ρ w, hw⟩ : Equiv.Perm (Fin 2300)) =
              c * (co2PermEquiv (w : K) : Equiv.Perm (Fin 2300)) * c⁻¹

@[expose] def SmithG1Input :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G), IsSimpleGroup G → SmithHyp G z →
    ∀ φ : centralizer ({z} : Set G) ≃* Cz, SmithGlobalHyps z φ →
      ∃ (G₁ : Subgroup G) (ψ : G₁ ≃* co2P0) (u v : G),
        (∀ h : G₁, (ψ h : Equiv.Perm (Fin 2300)) 3 = 3 → u * h * u⁻¹ ∈ G₁) ∧
        u ∉ normalizer (G₁ : Set G) ∧
        (∀ h : G₁, (ψ h : Equiv.Perm (Fin 2300)) 1 = 1 → v * h * v⁻¹ ∈ G₁) ∧
        v ∉ normalizer (G₁ : Set G) ∧
        (∀ x ∈ smithX G₁ u v, x * u ∈ smithX G₁ u v) ∧
        v ∈ closure ((G₁ : Set G) ∪ {u}) ∧
        centralizer ({z} : Set G) ≤ closure ((G₁ : Set G) ∪ {u})

end CFSG.Sporadic.Co2Smith
