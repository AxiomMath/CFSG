module

public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.EmptyFaithful.S153DInputs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417 CFSG.Assembly.LowTwoRank
open scoped commutatorElement

@[expose] def Lin2NatFixedPoints : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (n : ℕ), IsLin2Type L n →
    ∀ y ∈ L, Odd (orderOf y) → y ≠ 1 → ∀ a ∈ blockU L, y * a * y⁻¹ = a →
      a ∈ Subgroup.centralizer (L : Set G)

@[expose] def Lin2Setup : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15316 T Mc M V₁ V₂ Yp I L t → (∃ n : ℕ, 1 < n ∧ IsLin2Type L n) →
      Yp = YL153 Yp L ⊔ YC153 Yp L ∧ IsElemAbelianOfRank 3 2 (OTwoQuot Yp) ∧
        ∀ v ∈ VZ T M, ∃ a ∈ blockU L ⊓ Subgroup.centralizer ((R153 T V₁ Yp ⊓ L : Subgroup G) : Set G),
          ∃ b ∈ Subgroup.centralizer (L : Set G), v = a * b

@[expose] def Lin2NotCentralized : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15316 T Mc M V₁ V₂ Yp I L t → (∃ n : ℕ, 1 < n ∧ IsLin2Type L n) →
      ¬ YL153 Yp L ≤ Subgroup.centralizer (VZ T M : Set G) →
        ¬ Subgroup.normalizer (V₁ : Set G) ≤ M

end CFSG.Quasithin
