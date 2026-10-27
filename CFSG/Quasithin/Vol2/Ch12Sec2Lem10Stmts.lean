module

public import CFSG.Quasithin.H13.StatementsL2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

@[expose] def Out1222Fact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V : Subgroup G) [IsMulCommutative ↥V],
    (∀ v ∈ V, v ^ 2 = 1) → L ≤ Subgroup.normalizer (V : Set G) → ⁅V, L⁆ = V →
    (∀ J : Subgroup G, V ⊓ Subgroup.centralizer (L : Set G) ≤ J → J ≤ V →
      L ≤ Subgroup.normalizer (J : Set G) → J = V ⊓ Subgroup.centralizer (L : Set G) ∨ J = V) →
    pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G) → Modules12_2_2 L V →
      ∀ x ∈ Subgroup.normalizer (autOn L V : Set (MulAut ↥V)), ∃ k : ℕ,
        x ^ 2 ^ k ∈ autOn L V ⊔ Subgroup.centralizer (autOn L V : Set (MulAut ↥V))

@[expose] def End1222Fact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V : Subgroup G) [IsMulCommutative ↥V],
    (∀ v ∈ V, v ^ 2 = 1) → L ≤ Subgroup.normalizer (V : Set G) → ⁅V, L⁆ = V →
    (∀ J : Subgroup G, V ⊓ Subgroup.centralizer (L : Set G) ≤ J → J ≤ V →
      L ≤ Subgroup.normalizer (J : Set G) → J = V ⊓ Subgroup.centralizer (L : Set G) ∨ J = V) →
    pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G) → Modules12_2_2 L V →
      ∀ c : MulAut ↥V, (∀ y ∈ autOn L V, c * y = y * c) → c ∈ autOn L V

end CFSG.Quasithin.H13
