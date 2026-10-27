module

public import CFSG.RankThree.PartOne.S12.Sec1510Defs

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory

@[expose] noncomputable def thetaCore (p : ℕ) {G : Type} [Group G] (e : G) : Subgroup G :=
  inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({e} : Set G))

@[expose] def IsRegularIn (p : ℕ) {G : Type} [Group G] (E : Subgroup G) (e : G) : Prop :=
  ∀ B ∈ admissibleTriples p E, e ∉ B

@[expose] def CentralizesE (p : ℕ) {G : Type} [Group G] (E : Subgroup G) (e : G) : Prop :=
  ∀ x ∈ Subgroup.centralizer ({e} : Set G), x ∈ Subgroup.normalizer (E : Set G) →
    (∃ k : ℕ, x ^ (p ^ k) = 1) → ∀ y ∈ E, x * y = y * x

@[expose] def KFInnLayerFive : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152Five p E A (lieGenerated p E) →
    ∀ e ∈ E, e ≠ 1 → CentralizesE p E e → (∀ Z ∈ thetaComponentsAt p e, Z ≤ lieNormalizer p E) →
    ∀ x ∈ E, ∃ l ∈ E ⊓ thetaLayer p e,
      ∃ c' ∈ E ⊓ Subgroup.centralizer (thetaLayer p e : Set G), x = l * c'

@[expose] def KF1510E : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152Five p E A (lieGenerated p E) →
    ∀ e ∈ E, e ≠ 1 → CentralizesE p E e → (∀ Z ∈ thetaComponentsAt p e, Z ≤ lieNormalizer p E) →
    ∀ D : Subgroup G,
      (∀ x : G, x ∈ D ↔ x ∈ E ∧ ∀ l ∈ thetaLayer p e, x * l * x⁻¹ * l⁻¹ ∈ thetaCore p e) →
        IsCyclic ↥D ∨ p ^ 3 ≤ Nat.card ↥D ∨ ∃ A' ∈ admissibleTriples p E, D ≤ A'

end CFSG.RankThree.PartOne
