module

public import CFSG.Quasithin.Vol2.Ch11StatementsD

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)
open scoped IsMulCommutative

@[expose] def NatModuleOf {G : Type} [Group G] (L V : Subgroup G) (n : ℕ) : Prop :=
  ∃ _ : IsMulCommutative ↥V,
    (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      ∃ π : ↥(StatedSL 3 K) →* ↥(autOn L V),
        (FFModel.nat (StatedSL 3 K)).RealizesVia (V := ↥V) (autOn L V) ⊤
          ((Subgroup.centralizer (L : Set G)).subgroupOf V) π) ∨
    (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      ∃ π : ↥(StatedSp 2 K) →* ↥(autOn L V),
        (FFModel.nat (StatedSp 2 K)).RealizesVia (V := ↥V) (autOn L V) ⊤
          ((Subgroup.centralizer (L : Set G)).subgroupOf V) π) ∨
    G2NaturalDerived (V := ↥V) (autOn L V) ⊤ ((Subgroup.centralizer (L : Set G)).subgroupOf V) n

@[expose] def FactNPrimeNat : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V : Subgroup G) (n : ℕ) (hV : IsElemAbelian 2 V),
    2 ≤ n → L ≤ Subgroup.normalizer (V : Set G) → ⁅V, L⁆ = V → NatModuleOf L V n →
    ∀ X : Subgroup G, L ≤ X →
      X ⊓ Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) →
        E3.nPrime (autI hV X) ≤ n

@[expose] def TwoNaturalSum {G : Type} [Group G] (L U : Subgroup G) (n : ℕ) : Prop :=
  ∃ W₁ W₂ : Subgroup G, W₁ ≤ U ∧ W₂ ≤ U ∧
    L ≤ Subgroup.normalizer (W₁ : Set G) ∧ L ≤ Subgroup.normalizer (W₂ : Set G) ∧
    W₁ ⊓ W₂ = ⊥ ∧ W₁ ⊔ W₂ = U ∧
    (∃ _ : IsMulCommutative ↥W₁, BinaryNaturalSL (V := ↥W₁) (autOn L W₁) ⊤ ⊥ 3 n) ∧
    (∃ _ : IsMulCommutative ↥W₂, BinaryNaturalSL (V := ↥W₂) (autOn L W₂) ⊤ ⊥ 3 n) ∧
    IsXSectionIso₂ L W₁ ⊥ W₂ ⊥

theorem vmTwoNatural_iff {G : Type} [Group G] (T L I : Subgroup G) (n : ℕ) :
    VMTwoNatural T L I n ↔ TwoNaturalSum L (VM T L I) n :=
  Iff.rfl

@[expose] def FactNPrimeTwoNat : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L U : Subgroup G) (n : ℕ) (hU : IsElemAbelian 2 U),
    2 ≤ n → L ≤ Subgroup.normalizer (U : Set G) → TwoNaturalSum L U n →
    ∀ X : Subgroup G, L ≤ X →
      X ⊓ Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer (L : Set G) →
        E3.nPrime (autI hU X) ≤ 2 * n

@[expose] def FactCentralizerTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V : Subgroup G) (n : ℕ),
    IsElemAbelian 2 V → 2 ≤ n → L ≤ Subgroup.normalizer (V : Set G) → ⁅V, L⁆ = V →
    NatModuleOf L V n →
    ∀ x ∈ Subgroup.normalizer (V : Set G), x ∈ Subgroup.normalizer (L : Set G) →
      (∃ k : ℕ, x ^ 2 ^ k = 1) →
      (∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ Subgroup.centralizer (V : Set G)) →
        x ∈ Subgroup.centralizer (V : Set G)

@[expose] def RankTwoShape (X : Type) [Group X] (n : ℕ) : Prop :=
  (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 3) K)) ∨
    LieModel X .PSL 3 2 n ∨ LieModel X .PSp 2 2 n ∨ LieModel X .G2 0 2 n

@[expose] def SmallList443 (X : Type) [Group X] : Prop :=
  (∃ k : ℕ, 2 ≤ k ∧ LieModel X .PSL 2 2 k) ∨ LieModel X .PSL 3 2 1 ∨ LieModel X .PSL 4 2 1 ∨
    Nonempty (X ≃* alternatingGroup (Fin 6)) ∨ Nonempty (X ≃* alternatingGroup (Fin 7)) ∨
    (Group.IsPerfect X ∧ Nat.card (Subgroup.center X) = 3 ∧
      Nonempty (X ⧸ Subgroup.center X ≃* alternatingGroup (Fin 6))) ∨
    LieModel X .PSU 3 3 1

@[expose] def FactNotSmall443 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 2 ≤ n → RankTwoShape X n → ¬ SmallList443 X

end CFSG.Quasithin.Vol2.Ch11.SecB
