module

public import CFSG.Quasithin.Vol2.Ch7Inputs
public import CFSG.Quasithin.Background.HMathieuStatements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.H

@[expose] def HTab82 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (L M : Subgroup (MulAut V)), Mathieu.IsOver L M →
    (∀ n : ℕ, 1 ≤ n → BinaryNineTensor L ⊤ ⊥ n →
      CFSG.Open.pRank 2 M ≤ 4 * n ∧ ((4 * n : ℕ) : ℕ∞) ≤ betaH M ∧
        (n = 1 → (5 : ℕ∞) ≤ alphaE M) ∧ (1 < n → alphaE M = ⊤)) ∧
    (MathieuCode22 L ⊤ ⊥ →
      CFSG.Open.pRank 2 M ≤ 5 ∧ (6 : ℕ∞) ≤ betaH M ∧ (6 : ℕ∞) ≤ alphaE M) ∧
    (MathieuCode24 L ⊤ ⊥ →
      CFSG.Open.pRank 2 M ≤ 6 ∧ (6 : ℕ∞) ≤ betaH M ∧ (7 : ℕ∞) ≤ alphaE M)

@[expose] def HL3Nine82 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (L M : Subgroup (MulAut V)), Mathieu.IsOver L M →
    ∀ n : ℕ, 1 ≤ n → BinaryNineTensor L ⊤ ⊥ n →
      (∀ x ∈ M, x ≠ 1 → Odd (orderOf x) → rkIdx (fixV (Subgroup.zpowers x)) ≤ 4 * n →
        rk ↥(fixV (Subgroup.zpowers x)) = 5 * n) ∧
      (∀ A : Subgroup (MulAut V), A ≤ M → IsElemAbelian2 A →
        (3 * n ≤ rk ↥A ∨ A ≤ L ∧ n < rk ↥A) → 5 * n ≤ rkIdx (fixV A)) ∧
      (∀ A : Subgroup (MulAut V), A ≤ L → IsElemAbelian2 A → rk ↥A = 4 * n →
        ∀ x ∈ M ⊓ Subgroup.normalizer (A : Set (MulAut V)), orderOf x = 2 ^ (2 * n) - 1 →
          rk ↥(fixV (A ⊔ Subgroup.zpowers x)) ≠ 3 * n) ∧
      (∀ A : Subgroup (MulAut V), A ≤ M → IsElemAbelian2 A → 2 * n + 1 < rk ↥A → A ≤ L) ∧
      (n = 1 → ∀ y ∈ M, Odd (orderOf y) → rk ↥(fixV (Subgroup.zpowers y)) = 5 →
        M ⊓ centSub (fixV (Subgroup.zpowers y)) = Subgroup.zpowers y ∧ orderOf y = 3)

@[expose] def HCode82 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (L M : Subgroup (MulAut V)), Mathieu.IsOver L M →
    (MathieuCode24 L ⊤ ⊥ →
      (∀ x ∈ M, x ≠ 1 → Odd (orderOf x) → rkIdx (fixV (Subgroup.zpowers x)) ≤ 6 →
        orderOf x = 3 ∧ rkIdx (fixV (Subgroup.zpowers x)) = 6) ∧
      (∀ Y : Subgroup (MulAut V), Y ≤ M → Nat.card ↥Y = 3 → rkIdx (fixV Y) = 6 →
        M ⊓ centSub (fixV Y) = Y)) ∧
    ((MathieuCode22 L ⊤ ⊥ ∨ MathieuCode24 L ⊤ ⊥) →
      ∀ s : ℕ, (s = 2 ∨ s = 3) → ∀ A Y : Subgroup (MulAut V), A ≤ M → Y ≤ M →
        IsElemAbelian2 A → Nat.card ↥A = 2 ^ (2 * s) → Nat.card ↥Y = 3 → ⁅A, Y⁆ = A →
          rkIdx (fixV (A ⊔ Y)) ≠ 2 * (s + 1))

@[expose] def HOffNormal82 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (L M : Subgroup (MulAut V)), Mathieu.IsOver L M →
    ∀ S A : Subgroup (MulAut V), S ≤ M → IsPGroup 2 ↥S → ¬ 2 ∣ S.relIndex M → A ≤ S →
      IsElemAbelian2 A →
      ((BinaryNineTensor L ⊤ ⊥ 1 ∧ rk ↥A = 4 ∧ rk ↥(fixV A) = 4) ∨
        (MathieuCode22 L ⊤ ⊥ ∧ rk ↥A = 5 ∧ rkIdx (fixV A) = 6) ∨
        (MathieuCode24 L ⊤ ⊥ ∧ rk ↥A = 6 ∧ rkIdx (fixV A) = 7) ∨
        (MathieuCocode24 L ⊤ ⊥ ∧ rk ↥A = 6 ∧ rk ↥(fixV A) = 3)) →
      S ≤ Subgroup.normalizer (A : Set (MulAut V))

end CFSG.Quasithin.H13
