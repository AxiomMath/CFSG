module

public import CFSG.RankThree.PartTwo.Sec21.Item22Statements
public import CFSG.RankThree.PartTwo.Sec21.Item231

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

variable {G : Type} [Group G]

@[expose] def Item223OneConcl (A : Subgroup G) (φ : MulAut A) (Z : Subgroup G) : Prop :=
  ∃ m : ℕ, 1 < m ∧ Odd m ∧ Nonempty (Z ≃* projSU 4 2 m) ∧
    Nonempty (kOf A φ ≃* projSL 2 (GaloisField 2 m))

@[expose] def Item228OneConcl (A : Subgroup G) (φ : MulAut A) (Z : Subgroup G) : Prop :=
  ∃ m : ℕ, 0 < m ∧ Even m ∧ Nonempty (kOf A φ ≃* projSL 2 (GaloisField 2 m)) ∧
    (Nonempty (Z ≃* SL3 m) ∨ Nonempty (Z ≃* projSp 2 (GaloisField 2 m)) ∨
      Nonempty (Z ≃* projSU 4 2 m) ∨ (m % 4 = 0 ∧ Nonempty (Z ≃* projSU 4 2 (m / 2))) ∨
      ((m = 2 ∨ m = 4) ∧ Nonempty (Z ≃* projSU 5 2 2)))

@[expose] def Item233KLeComponent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → ∀ B : Subgroup G, B ≤ A → Nat.card B = 3 →
      ∀ X : Subgroup (iGroup A ⊓ Subgroup.centralizer (B : Set G) : Subgroup G),
        CFSG.IsComponent X → ∃ φ ∈ dStar A,
          kOf A φ ≤ X.map (iGroup A ⊓ Subgroup.centralizer (B : Set G)).subtype

@[expose] def TerminalRootComponents : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (I A : Subgroup G), A ≤ I → IsElemAbelian 3 A →
    ((Nonempty (I ≃* projSU 5 2 3) ∧ Nat.card A = 3 ^ 4) ∨
      (Nonempty (I ≃* projSL 4 (GaloisField 2 2)) ∧ Nat.card A = 3 ^ 3) ∨
      (Nonempty (I ≃* projSp 3 (GaloisField 2 2)) ∧ Nat.card A = 3 ^ 3)) →
    ∀ D : Set (MulAut A), (∀ φ ∈ D, IsReflectionOn φ) →
      (∀ g ∈ starOf A I, ∀ φ ∈ D, g * φ * g⁻¹ ∈ D) → Subgroup.closure D = starOf A I →
      ∀ B : Subgroup G, B ≤ A → Nat.card B = 3 →
        ∀ X : Subgroup (I ⊓ Subgroup.centralizer (B : Set G) : Subgroup G),
          CFSG.IsComponent X → ∃ φ ∈ D, ∀ P : Subgroup G, P ≤ I →
            P ≤ Subgroup.centralizer (fixedInG A φ : Set G) → Group.IsPerfect P →
              P ≤ X.map (I ⊓ Subgroup.centralizer (B : Set G)).subtype

@[expose] def Item233ZGen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Item231Concl A → ∀ φ ∈ dStar A, ∀ Z ∈ lStar A, kOf A φ ≤ Z →
      (Nat.card A = 3 ^ 4 → Item223OneConcl A φ Z) →
      (Nat.card A = 3 ^ 3 → ∀ ψ ∈ dStar A, ψ ≠ φ → Item228OneConcl A φ Z) →
        Z ≤ ⨆ (ψ : MulAut A) (_ : ψ ∈ dStar A) (_ : ψ ∈ starOf A Z), kOf A ψ

end CFSG.RankThree.PartTwo.Sec21
