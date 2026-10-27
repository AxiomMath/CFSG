module

public import CFSG.Quasithin.Background.E2Two
public import CFSG.Quasithin.Background.E2Pair
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.ASInputs

open CFSG.Open CFSG.QuasithinUnique

section Defs

variable {G : Type} [Group G]

abbrev pairB (M V X : Subgroup G) : Subgroup G := kerIn M X ⊓ V

abbrev pairP (M V X : Subgroup G) (g : G) : Subgroup G :=
  pairB M V X ⊔ B6.conjSub g (pairB M V X)

end Defs

@[expose] def AS_E_2_10_seven : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T M V : Subgroup G) (g : G), E2.Pair X T M V g →
    (∃ n : ℕ, 1 < n ∧ (IsPSL 2 2 n (E2.StarQuot M X) ∨ IsSz n (E2.StarQuot M X))) →
      kerIn M X = pCoreOf 2 X ∧
      (∃ E : Subgroup G, pairP M V X g ≤ E ∧ E ≤ X ∧ (∀ x ∈ E, x ^ 2 ∈ pairP M V X g) ∧
        (∀ x ∈ E, ∀ y ∈ E, x * y * x⁻¹ * y⁻¹ ∈ pairP M V X g) ∧
        ⁅E, oTwoUpper X⁆ ≤ pairP M V X g ∧
        E ⊓ (oTwoUpper X ⊔ pairP M V X g) = pairP M V X g ∧
        E ⊔ (oTwoUpper X ⊔ pairP M V X g) = X) ∧
      ((pCoreOf 2 (oTwoUpper X ⊔ pairP M V X g) = pairP M V X g ∧
          ∃ (_ : ((pairP M V X g).subgroupOf (oTwoUpper X ⊔ pairP M V X g)).Normal),
            Nonempty (↥(oTwoUpper X ⊔ pairP M V X g) ⧸
                (pairP M V X g).subgroupOf (oTwoUpper X ⊔ pairP M V X g) ≃*
              E2.StarQuot M X)) ∨
        ∃ Z : Subgroup G, pairP M V X g ≤ Z ∧ Z ≤ oTwoUpper X ⊔ pairP M V X g ∧
          (∀ z ∈ Z, ∃ k : ℕ, z ^ 2 ^ k ∈ pairP M V X g) ∧
          ⁅Z, oTwoUpper X ⊔ pairP M V X g⁆ ≤ pairP M V X g ∧
          ⁅oTwoUpper X ⊔ pairP M V X g, oTwoUpper X ⊔ pairP M V X g⁆ ⊔ pairP M V X g =
            oTwoUpper X ⊔ pairP M V X g ∧
          ∃ (_ : (Z.subgroupOf (oTwoUpper X ⊔ pairP M V X g)).Normal),
            IsSz 3 (↥(oTwoUpper X ⊔ pairP M V X g) ⧸
              Z.subgroupOf (oTwoUpper X ⊔ pairP M V X g)))

@[expose] def AS_E_2_10_eight : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T M V : Subgroup G) (g : G), E2.Pair X T M V g →
    (∃ n : ℕ, 1 ≤ n ∧ IsPSp4 2 n (E2.StarQuot M X)) →
      pCoreOf 2 X = kerIn M X ∧
      (∃ C E : Subgroup G, pairP M V X g ≤ C ∧ C ≤ X ∧ pairP M V X g ≤ E ∧ E ≤ X ∧
        (∃ (_ : ((pairP M V X g).subgroupOf C).Normal),
          Nonempty (↥C ⧸ (pairP M V X g).subgroupOf C ≃* E2.StarQuot M X)) ∧
        (∀ x ∈ E, x ^ 2 ∈ pairP M V X g) ∧
        (∀ x ∈ E, ∀ y ∈ E, x * y * x⁻¹ * y⁻¹ ∈ pairP M V X g) ∧
        ⁅C, E⁆ ≤ pairP M V X g ∧ C ⊓ E = pairP M V X g ∧ C ⊔ E = X) ∧
      pCoreOf 2 (oTwoUpper X ⊔ pairP M V X g) = pairP M V X g ∧
      ∃ (_ : ((pairP M V X g).subgroupOf (oTwoUpper X ⊔ pairP M V X g)).Normal),
        Nonempty (↥(oTwoUpper X ⊔ pairP M V X g) ⧸
            (pairP M V X g).subgroupOf (oTwoUpper X ⊔ pairP M V X g) ≃*
          ↥(commutator (E2.StarQuot M X)))

end CFSG.Quasithin.ASInputs
