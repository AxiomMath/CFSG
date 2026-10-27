module

public import CFSG.RankThree.PartOne.S9.Defs

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory
open scoped commutatorElement

@[expose] def PGOddSecondCenterPrimeTorsion : Prop :=
  ∀ (P : Type) [Group P] [Finite P] (p : ℕ), p.Prime → p ≠ 2 → IsPGroup p P →
    (Subgroup.closure {x : P | x ∈ Subgroup.upperCentralSeries P 2 ∧ x ^ p = 1}).Characteristic ∧
    (∀ x : P, x ∈ Subgroup.closure {x : P | x ∈ Subgroup.upperCentralSeries P 2 ∧ x ^ p = 1} ↔
      x ∈ Subgroup.upperCentralSeries P 2 ∧ x ^ p = 1) ∧
    (∀ w ∈ Subgroup.closure {x : P | x ∈ Subgroup.upperCentralSeries P 2 ∧ x ^ p = 1}, ∀ g : P,
      ⁅w, g⁆ ∈ Subgroup.center P ∧ ⁅w, g⁆ ^ p = 1) ∧
    (¬ IsCyclic P →
      ¬ IsCyclic (Subgroup.closure {x : P | x ∈ Subgroup.upperCentralSeries P 2 ∧ x ^ p = 1}))

@[expose] def PlaneFamilyProductCoreNormalizer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → p ≠ 2 → ∀ P : Subgroup G,
    IsPGroup p P → ∀ f : Subgroup G → Subgroup G,
    (∀ E F : Subgroup G, E ≤ P → F ≤ P → IsElementaryAbelian p E → Nat.card E = p ^ 2 →
      IsElementaryAbelian p F → Nat.card F = p ^ 2 → ⁅E, F⁆ = ⊥ → f E = f F) →
    (∀ E : Subgroup G, E ≤ P → IsElementaryAbelian p E → Nat.card E = p ^ 2 → ∀ g : G,
      conjugate E g ≤ P → conjugate (f E) g = f (conjugate E g)) →
    ∀ E₀ : Subgroup G, E₀ ≤ P → IsElementaryAbelian p E₀ → Nat.card E₀ = p ^ 2 →
      3 ≤ CFSG.Assembly.pRank p (P ⊓ Subgroup.centralizer (E₀ : Set G)) →
      aschCore 2 p P ≤ Subgroup.normalizer (f E₀ : Set G)

@[expose] def AlphaRankThreeLocalCompletion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → p ≠ 2 → ∀ A : Subgroup G,
    IsElementaryAbelian p A → Nat.card A = p ^ 3 → LocalAlphaBound p A →
    (∀ B : Subgroup G, B ≤ A → Nat.card B = p ^ 2 → IsPGroup 2 (twoCoreAlpha B)) ∧
    ∀ B D : Subgroup G, B ≤ A → Nat.card B = p ^ 2 → D ≤ A → Nat.card D = p ^ 2 →
      twoCoreAlpha B = twoCoreAlpha D

@[expose] def AlphaGlobalPlaneRelations : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → p ≠ 2 →
    (∀ A : Subgroup G, IsElementaryAbelian p A → Nat.card A = p ^ 3 → LocalAlphaBound p A) →
    (∀ E F : Subgroup G, IsElementaryAbelian p E → Nat.card E = p ^ 2 →
      IsElementaryAbelian p F → Nat.card F = p ^ 2 → ⁅E, F⁆ = ⊥ →
      twoCoreAlpha E = twoCoreAlpha F) ∧
    ∀ E : Subgroup G, IsElementaryAbelian p E → Nat.card E = p ^ 2 →
      (∃ A : Subgroup G, E ≤ A ∧ IsElementaryAbelian p A ∧ Nat.card A = p ^ 3) →
      IsPGroup 2 (twoCoreAlpha E)

@[expose] def AlphaProductCoreLocalNormalizer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → p ≠ 2 →
    (∀ A : Subgroup G, IsElementaryAbelian p A → Nat.card A = p ^ 3 → LocalAlphaBound p A) →
    ∀ P : Subgroup G, IsPGroup p P → ∀ E : Subgroup G, E ≤ P → IsElementaryAbelian p E →
      Nat.card E = p ^ 2 → 3 ≤ CFSG.Assembly.pRank p (P ⊓ Subgroup.centralizer (E : Set G)) →
      IsPGroup 2 (twoCoreAlpha E) ∧ aschCore 2 p P ≤ Subgroup.normalizer (twoCoreAlpha E : Set G) ∧
        (twoCoreAlpha E ≠ ⊥ → IsTwoLocal (Subgroup.normalizer (twoCoreAlpha E : Set G)))

@[expose] def SectionNinePlaneCommutatorBound : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), Sec9Hyp G p → GoodGlobalRank G p →
    ∀ A : Subgroup G, IsElementaryAbelian p A → Nat.card A = p ^ 3 →
    ∀ c ∈ A, c ≠ 1 → ∀ B : Subgroup G, B ≤ A → Nat.card B = p ^ 2 → c ∈ B →
      ⁅inSubgroup (pCore 2) (Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
          Subgroup.centralizer (B : Set G)), A⁆ ≤
        inSubgroup (pCore 2) (Subgroup.normalizer (Subgroup.zpowers c : Set G))

@[expose] def SectionNineUniformAlphaVerification : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), Sec9Hyp G p → GoodGlobalRank G p →
    ∀ A : Subgroup G, IsElementaryAbelian p A → Nat.card A = p ^ 3 →
      LocalAlphaBound p A ∧
      (∀ B : Subgroup G, B ≤ A → Nat.card B = p ^ 2 → IsPGroup 2 (twoCoreAlpha B)) ∧
      ∀ B D : Subgroup G, B ≤ A → Nat.card B = p ^ 2 → D ≤ A → Nat.card D = p ^ 2 →
        twoCoreAlpha B = twoCoreAlpha D

end CFSG.RankThree.PartOne
