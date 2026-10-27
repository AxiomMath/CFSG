module

public import CFSG.Quasithin.Vol2.Ch11SecSSetup
public import CFSG.Quasithin.Background.OperatorJordanHolder

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Assembly.LowTwoRank (StatedSL)

@[expose] def LemmaB414Head : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Γ V Z L X : Subgroup G) (F : Type) [Field F] [Fintype F],
    Fintype.card F = 4 →
    Γ ≤ Subgroup.normalizer (V : Set G) → Γ ≤ Subgroup.normalizer (Z : Set G) → Z < V →
    (∀ v ∈ V, v ^ 2 ∈ Z) → (∀ v ∈ V, ∀ w ∈ V, v * w * v⁻¹ * w⁻¹ ∈ Z) →
    (∀ J : Subgroup G, Z ≤ J → J ≤ V → Γ ≤ Subgroup.normalizer (J : Set G) → J = Z ∨ J = V) →
    L ≤ Γ → X ≤ Γ →
    ∀ α : ↥Γ →* GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F), Function.Surjective α →
    (∀ γ : ↥Γ, α γ = 1 → ∀ v ∈ V, (γ : G) * v * (γ : G)⁻¹ * v⁻¹ ∈ Z) →
    (∃ γ : ↥Γ, α γ ∈ commutator (GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F)) ∧
      ∃ v ∈ V, (γ : G) * v * (γ : G)⁻¹ * v⁻¹ ∉ Z) →
    ⁅(L.subgroupOf Γ).map α, (L.subgroupOf Γ).map α⁆ = (L.subgroupOf Γ).map α →
    (L.subgroupOf Γ).map α ≠ ⊥ →
    (L.subgroupOf Γ).map α ≠ commutator (GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F)) →
    (∃ S : Subgroup (GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F)),
      QuasithinUnique.IsSylowTwoOf S ⊤ ∧
        S ≤ Subgroup.normalizer (((L.subgroupOf Γ).map α : Subgroup _) : Set _)) →
    Nat.card ↥((X.subgroupOf Γ).map α) = 3 →
    (∀ y ∈ X, ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ pCoreOf 2 L) →
    ∀ α₀ : ↥L →* ↥(StatedSL 2 F), Function.Surjective α₀ →
    α₀.ker = (pCoreOf 2 L).subgroupOf L →
    ∀ γx : ↥Γ, (γx : G) ∈ X → α γx ≠ 1 →
    (∃ l : List (Subgroup G × Option F), IsLabSeries (L ⊔ X) L (γx : G) α₀ Z l V) →
      ∃ (μ : F) (j : ℕ), j < 3 ∧ μ ^ 3 = 1 ∧
        (∃ l : List (Subgroup G × Option F), IsLabSeries (L ⊔ X) L (γx : G) α₀ Z l V ∧
          labMultiset l = ({μ ^ (j + 1), (μ ^ j)⁻¹, μ ^ j * μ⁻¹} : Multiset F)) ∧
        (j = 0 → ∀ J : Subgroup G, ⁅V, pCoreOf 2 L⁆ ⊔ Z ≤ J → J ≤ V →
          (∀ v ∈ V, (γx : G) * v * (γx : G)⁻¹ * v⁻¹ ∈ J) → J = V)

@[expose] def Obl11_1_2StarSL3Ab : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I V₁ V₂ X K : Subgroup G),
    StarHyp G T L I V₁ V₂ X K → KindSL3 L (fsuV T I) 2 →
      ¬ conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) ≤ pCoreOf 2 (L ⊔ T)

end CFSG.Quasithin.Vol2.Ch11.SecS
