module

public import CFSG.RankThree.PartOne.S12.Equivariance
public import CFSG.RankThree.PartOne.S12.Facts

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory

variable {G : Type} [Group G]

@[expose] def zeroLayer (p : ℕ) (E : Subgroup G) (b : G) : Subgroup G :=
  Subgroup.closure {x : G | ∃ Y ∈ thetaCompZeroE p E, Y ∈ thetaComponentsAt p b ∧ x ∈ Y}

@[expose] def thetaCompCentralizer (p : ℕ) (D : Subgroup G) : Set (Subgroup G) :=
  (fun L : Subgroup (Subgroup.centralizer (D : Set G)) =>
      L.map (Subgroup.centralizer (D : Set G)).subtype) ''
    thetaComponents p (Subgroup.centralizer (D : Set G))

@[expose] def KF156' : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152 p E A (lieGenerated p E) →
    ∀ X ∈ thetaCompZeroE p E, X ≤ lieGenerated p E

@[expose] def KF157 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152 p E A (lieGenerated p E) →
    ∀ X ∈ thetaCompZeroE p E,
      (∀ e ∈ E, ∃ x ∈ X, ∃ y ∈ Subgroup.centralizer (X : Set G), e = x * y) ∧
        ¬ p ∣ Nat.card ↥(X ⊓ Subgroup.centralizer (X : Set G))

@[expose] def KF158A : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152 p E A (lieGenerated p E) →
    ∃ t ∈ reflectionSet p E, ∃ K J : Subgroup G, IsKt p E t K ∧ K ≤ J ∧ autMovedInG E t ≤ K ∧
      p * Nat.card ↥(A ⊓ Subgroup.centralizer (J : Set G)) = Nat.card ↥A ∧
      J ∈ thetaCompCentralizer p (A ⊓ Subgroup.centralizer (J : Set G)) ∧
      ∃ S : Subgroup G, S ≤ J ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧ A ≤ Subgroup.normalizer (S : Set G) ∧
        S = ⁅S, A⁆

@[expose] def KF158L0 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152 p E A (lieGenerated p E) →
    ∀ b ∈ E, b ≠ 1 → ∀ z ∈ Subgroup.centralizer ({b} : Set G),
      ∀ Y ∈ thetaCompZeroE p E, Y ∈ thetaComponentsAt p b → conjBy z Y ∈ thetaCompZeroE p E

@[expose] def KF158Comm : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152 p E A (lieGenerated p E) →
    ∀ b ∈ E, b ≠ 1 →
      ∀ Y₁ ∈ thetaCompZeroE p E, Y₁ ∈ thetaComponentsAt p b →
        ∀ Y₂ ∈ thetaCompZeroE p E, Y₂ ∈ thetaComponentsAt p b → Y₁ ≠ Y₂ →
          Y₁ ≤ Subgroup.centralizer (Y₂ : Set G)

@[expose] def KF158Cov : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152 p E A (lieGenerated p E) →
    ∀ t ∈ reflectionSet p E, ∀ a : G, Subgroup.zpowers a = autMovedInG E t →
      (E ≤ zeroLayer p E a ⊔ Subgroup.zpowers a) ∨
      (Outcome152One p E A (lieGenerated p E) ∧ ∃ d ∈ E, d ≠ 1 ∧
        d ∈ zeroLayer p E a ⊔ Subgroup.zpowers a ∧ E ≤ zeroLayer p E d ⊔ Subgroup.zpowers d) ∨
      (Outcome152Five p E A (lieGenerated p E) ∧ ∃ w ∈ torusNormalizer E,
        w * a * w⁻¹ ∈ zeroLayer p E a ∧
        zeroLayer p E a ⊔ conjBy w (zeroLayer p E a) = lieGenerated p E)

end CFSG.RankThree.PartOne
