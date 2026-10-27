module

public import CFSG.Quasithin.Background.F6Cat
public import CFSG.Quasithin.EmptyFaithful.T1531InspBasic
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def A5HatGeom153 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (I V₀ X P V V₁ V₂ : Subgroup G) (Q : Subgroup ↥I) [Q.Normal],
    V₀ ≤ I → I ≤ Subgroup.normalizer (V₀ : Set G) → IsElemAbelian 2 V₀ → Nat.card ↥V₀ = 2 ^ 6 →
    Q = (I ⊓ Subgroup.centralizer (V₀ : Set G)).subgroupOf I →
    F6.IsHatSym 6 (↥I ⧸ Q) →
    X ≤ I → oTwoUpper (⊤ : Subgroup (↥I ⧸ Q)) ≤ barQ I Q X →
    V ≤ V₀ → V₁ ≤ V → V₂ ≤ V → V₁ ⊓ V₂ = ⊥ → V₁ ⊔ V₂ = V → Nat.card ↥V₁ = 4 →
    Nat.card ↥V₂ = 4 →
    P ≤ I → IsPGroup 2 ↥P → ¬ P ≤ Q.map I.subtype → P ≤ Subgroup.centralizer (V : Set G) →
    (∀ x ∈ X, x ∈ Subgroup.normalizer (V : Set G) →
      (∀ v ∈ V₁, x * v * x⁻¹ ∈ V₁) ∨ (∀ v ∈ V₁, x * v * x⁻¹ ∈ V₂)) →
    ¬ Group.IsSolvable ↥(X ⊓ Subgroup.normalizer (V₁ : Set G))

@[expose] def InspectL3Normal153 : Prop :=
  ∀ (D : Type) [Group D] [Finite D] (D₁ D₂ N : Subgroup D),
    IsGoldschmidtAmalgam D₁ D₂ → F6.F618ConclusionCat D₁ D₂ → N.Normal →
    oTwoUpper (⊤ : Subgroup D) ≤ N → Nonempty (↥N ≃* ↥(StatedSL 3 (ZMod 2))) → N = ⊤

end CFSG.Quasithin
