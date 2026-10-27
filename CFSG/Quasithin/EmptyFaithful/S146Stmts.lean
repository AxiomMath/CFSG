module

public import CFSG.Quasithin.EmptyFaithful.S146Defs
public import CFSG.Quasithin.EmptyFaithful.S145Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def Stage1461Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ H : Subgroup G, IsHTM T M H → ∀ p : ℕ, p.Prime → p ≠ 2 →
      oTwoPIn p H ⊓ M = pCoreOf 2 H

@[expose] def Stage1461Three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ H : Subgroup G, IsHTM T M H → ∀ K ∈ cComp H, ¬ K ≤ M

@[expose] def Stage1461Four : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ H : Subgroup G, IsHTM T M H → ∀ X : Subgroup G, X ≠ ⊥ → oTwoUpper X = X → X ≤ H →
      (X.subgroupOf H).Normal → IsHTM T M (X ⊔ T)

@[expose] def Stage1461Five : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ H : Subgroup G, IsHTM T M H →
      oTwoFstarIn H ≤ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 H) : Set G)

@[expose] def Stage1461Six : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ H : Subgroup G, IsHTM T M H → ∀ T₁ : Subgroup G, pCoreOf 2 H ≤ T₁ → T₁ ≤ T →
      (T₁.subgroupOf T).Normal →
        Subgroup.normalizer (T₁ : Set G) ≤ Subgroup.normalizer (omegaOneCenterOf T₁ : Set G) ∧
          Subgroup.normalizer (omegaOneCenterOf T₁ : Set G) ≤ mcOf T

@[expose] def Stage1463One : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ H : Subgroup G, IsHTM T M H → ∀ u : G, IsInvU T M H u →
      (tU T u).relIndex T = 4 ∧ (tU T u).relIndex (tZero T u) = 2 ∧
        tZero T u = T ⊓ Subgroup.normalizer (tU T u : Set G) ∧
        tZero T u = pCoreOf 2 (mcOf T) ⊔ tU T u ∧ tZero T u = pCoreOf 2 H ⊔ tU T u

@[expose] def Stage1463Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ H : Subgroup G, IsHTM T M H → ∀ u : G, IsInvU T M H u →
      Subgroup.normalizer (tZero T u : Set G) = T

@[expose] def Stage1463Three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ H : Subgroup G, IsHTM T M H → ∀ u : G, IsInvU T M H u →
      ¬ (pCoreOf 2 H ⊓ Subgroup.centralizer ({u} : Set G) ≤ Subgroup.centralizer (VZ T M : Set G)) ∧
        yOfL22 T M = ⁅yOfL22 T M, pCoreOf 2 (mcOf T) ⊓ Subgroup.centralizer ({u} : Set G)⁆ ∧
        yOfL22 T M = ⁅yOfL22 T M, pCoreOf 2 H ⊓ Subgroup.centralizer ({u} : Set G)⁆

@[expose] def Stage1463Four : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ H : Subgroup G, IsHTM T M H → ∀ u : G, IsInvU T M H u →
      Subgroup.normalizer (tU T u : Set G) = tZero T u ∧
        IsSylowTwoOf (tU T u) (Subgroup.centralizer ({u} : Set G)) ∧
        ∀ (g : G) (z : G), z ∈ quasithinOmegaOneCenter T → z ≠ 1 → g * z * g⁻¹ ≠ u

end CFSG.Quasithin
