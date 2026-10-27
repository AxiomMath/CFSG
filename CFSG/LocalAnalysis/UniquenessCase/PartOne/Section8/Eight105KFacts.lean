module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102KFacts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def KU45Lines : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), IsU45 X n →
    ∀ S : Subgroup X, IsPGroup 3 S → ¬ 3 ∣ S.index →
      (∀ x ∈ S, ∀ y ∈ S, x * y = y * x) ∧
      ∀ B₀ : Subgroup X, F08.NotationB8103 ⊤ S n B₀ →
        ∃ B₁ : Subgroup X, B₁ ≤ F08.KOf8103 ⊤ B₀ ∧ F08.NotationB8103 ⊤ S n B₁ ∧ B₁ ≠ B₀ ∧
          ∀ Y : Subgroup X, F08.NotationB8103 ⊤ S n Y → Y = B₀ ∨ Y = B₁

@[expose] def KU45CentP : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), IsU45 X n →
    ∀ p : ℕ, p.Prime → p ∣ 2 ^ n + 1 →
      ∀ S : Subgroup X, IsPGroup 3 S → ¬ 3 ∣ S.index →
        ∀ B₀ : Subgroup X, F08.NotationB8103 ⊤ S n B₀ →
          ∃ D₀ : Subgroup X, D₀ ≤ F08.KOf8103 ⊤ B₀ ∧ Nat.card D₀ = p ∧
            D₀ ≤ centralizer (S : Set X)

@[expose] def KU45GenRank : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), IsU45 X n →
    ∀ p : ℕ, p.Prime → p ∣ 2 ^ n + 1 →
      ∀ S : Subgroup X, IsPGroup 3 S → ¬ 3 ∣ S.index →
        ∀ B₀ B₁ : Subgroup X, F08.NotationB8103 ⊤ S n B₀ → F08.NotationB8103 ⊤ S n B₁ →
          B₀ ≠ B₁ → 2 ≤ Open.pRank p (F08.KOf8103 ⊤ B₀ ⊔ F08.KOf8103 ⊤ B₁)

@[expose] def KU45AutOdd : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), IsU45 X n →
    ∀ S : Subgroup X, IsPGroup 3 S → ¬ 3 ∣ S.index →
      ∀ B₀ : Subgroup X, F08.NotationB8103 ⊤ S n B₀ →
        ∀ α : MulAut X, (∃ k : ℕ, α ^ (2 ^ k) = 1) →
          (∀ x ∈ F08.KOf8103 ⊤ B₀, α x = x) → (∀ s ∈ S, α s = s) → α = 1

@[expose] def KU45Radical : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), IsU45 X n →
    ∀ S : Subgroup X, IsPGroup 3 S → ¬ 3 ∣ S.index →
      ∀ B₀ : Subgroup X, F08.NotationB8103 ⊤ S n B₀ →
        ∃ Y₁ Y₂ : Subgroup X,
          (∀ Y ∈ ({Y₁, Y₂} : Set (Subgroup X)),
            Y ≠ ⊤ ∧ (∃ T₀ : Sylow 2 X, normalizer ((T₀ : Subgroup X) : Set X) ≤ Y) ∧
              F08.KOf8103 ⊤ B₀ ⊔ S ≤ Y ∧ pCoreOf 2 Y ≠ ⊥ ∧
              F08.KOf8103 ⊤ B₀ ⊓ pCoreOf 2 Y = ⊥ ∧
              ∀ T₀ : Sylow 2 X, pCoreOf 2 Y ≤ (T₀ : Subgroup X) →
                normalizer ((T₀ : Subgroup X) : Set X) ≤ Y) ∧
          pCoreOf 2 Y₁ ⊓ Y₂ = ⊥ ∧ pCoreOf 2 Y₂ ⊓ Y₁ = ⊥ ∧
          ∀ Z : Subgroup X, Z ≠ ⊤ →
            (∃ T₀ : Sylow 2 X, normalizer ((T₀ : Subgroup X) : Set X) ≤ Z) →
              F08.KOf8103 ⊤ B₀ ⊔ S ≤ Z → Z = Y₁ ∨ Z = Y₂

@[expose] def KU45BorelOrders : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), IsU45 X n →
    ∀ (T₀ : Sylow 2 X) (Z₁ Z₂ : Subgroup X), normalizer ((T₀ : Subgroup X) : Set X) ≤ Z₁ →
      normalizer ((T₀ : Subgroup X) : Set X) ≤ Z₂ → Nat.card Z₁ = Nat.card Z₂ → Z₁ = Z₂

@[expose] def KSuzukiL2 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (I K : Subgroup Y), CFSG.Open.IsKGroup I → ¬ 3 ∣ Nat.card I →
    (∀ r : ℕ, r.Prime → r ≠ 2 → Open.pRank r I ≤ 3) → K ≤ normalizer (I : Set Y) →
    ⁅K, K⁆ = K → ∀ m : ℕ, 4 ≤ m → UC22.IsL2 (Bar2 K) m → ⁅I, K⁆ ≤ pCoreOf 2 I

@[expose] def KU3Ident : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsKGroup Y → CFSG.pPrimeCore 3 Y = ⊥ →
    ∀ (X K D₀ : Subgroup Y) (n p : ℕ), X.Normal → Open.pRank 3 X = 1 →
      X = Subgroup.normalClosure (K : Set Y) → ⁅K, K⁆ = K → UC22.IsL2 (Bar2 K) (2 * n) → 2 ≤ n →
      Even n → p.Prime → p ∣ 2 ^ n + 1 → D₀ ≤ K → Nat.card D₀ = p →
      X ⊓ centralizer (D₀ : Set Y) ≤ normalizer (K : Set Y) → X ≠ K → UC22.IsU3 X (2 * n)

@[expose] def KU3Mult : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Z : Subgroup X) [Z.Normal] (f : ℕ), Z ≤ center X →
    ¬ 3 ∣ Nat.card Z → UC22.IsU3 (X ⧸ Z) f → 4 ≤ f → Even f →
      Subgroup.closure {x : X | x ^ 3 = 1} = ⊤ → Z = ⊥

@[expose] def KU3Facts : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (f : ℕ), UC22.IsU3 X f → 4 ≤ f → Even f →
    ∀ K : Subgroup X, ⁅K, K⁆ = K → UC22.IsL2 (Bar2 K) f →
      (∀ U : Subgroup X, IsPGroup 2 U → K ≤ normalizer (U : Set X) → U = ⊥) ∧
      (∀ T₂ : Sylow 2 X, ¬ (T₂ : Subgroup X) ≤ normalizer (K : Set X)) ∧
      ∃ g ∈ centralizer (K : Set X), orderOf g = 2 ^ f + 1 ∧
        ∀ A : Subgroup (MulAut X), IsPGroup 2 A → (∀ α ∈ A, ∀ x ∈ K, α x = x) →
          Nat.card A ≤ 2 ∧ ∀ α ∈ A, α ≠ 1 → α g = g⁻¹

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
