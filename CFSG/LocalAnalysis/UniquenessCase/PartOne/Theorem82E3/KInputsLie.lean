module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open Subgroup
open scoped commutatorElement
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
  (LieFam811 IsLie811 qPlusPi qMinusPi IsSignedCoords)

@[expose] def LieOddCharRank : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], ∀ (fam : LieFam811) (r f : ℕ), IsLie811 Y fam r f →
    r ≠ 2 → 4 ≤ pRank r (⊤ : Subgroup Y)

@[expose] def LieL67PlusRank : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], ∀ (fam : LieFam811) (f : ℕ), (fam = .l6 ∨ fam = .l7) →
    IsLie811 Y fam 2 f → ∀ p : ℕ, p.Prime → 5 ≤ p → p ∣ qPlusPi 2 f →
      4 ≤ pRank p (⊤ : Subgroup Y)

@[expose] def K7cSharp : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], ∀ (fam : LieFam811) (f : ℕ),
    (fam = .psp6 ∨ fam = .pomega8m ∨ fam = .l4) → IsLie811 Y fam 2 f →
      ∀ p : ℕ, p.Prime → 5 ≤ p → ¬ p ∣ 2 ^ f * (2 ^ (2 * f) - 1) →
        pRank p (⊤ : Subgroup Y) ≤ 1

@[expose] def K7L67TwoSharp : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], ∀ (fam : LieFam811), (fam = .l6 ∨ fam = .l7) →
    IsLie811 Y fam 2 1 → ∀ p : ℕ, p.Prime → 5 ≤ p → p ≠ 7 → pRank p (⊤ : Subgroup Y) ≤ 1

@[expose] def K7L4Mech : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], ∀ f : ℕ, IsLie811 Y .l4 2 f →
    ∀ p : ℕ, p.Prime → 5 ≤ p → p ∣ qPlusPi 2 f →
    ∀ A : Subgroup Y, IsElemAbelian 3 A → Nat.card A = 27 →
      ¬ p ∣ Nat.card (centralizer (A : Set Y)) ∧
      ∀ X : Subgroup Y, X ≤ A → Nat.card X = 3 → p ∣ Nat.card (centralizer (X : Set Y))

@[expose] def K7L7TwoMech : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsLie811 Y .l7 2 1 →
    ∀ A : Subgroup Y, IsElemAbelian 3 A → Nat.card A = 27 →
      ¬ 7 ∣ Nat.card (centralizer (A : Set Y)) ∧
      ∀ X : Subgroup Y, X ≤ A → Nat.card X = 3 → 7 ∣ Nat.card (centralizer (X : Set Y))

@[expose] def K7Sp6Planes : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], ∀ f : ℕ, IsLie811 Y .psp6 2 f →
    ∀ p : ℕ, p.Prime → 5 ≤ p → p ∣ qPlusPi 2 f →
    ∀ A : Subgroup Y, IsElemAbelian 3 A → Nat.card A = 27 →
    ∀ c, IsSignedCoords A c →
      1 ≤ pRank p (centralizer ({c (.ofAdd ![1, 0, 0]), c (.ofAdd ![0, 1, 0])} : Set Y)) ∧
      ∀ v : Fin 3 → ZMod 3, v ≠ 0 → (∃ i, v i = 0) →
        2 ≤ pRank p (centralizer ({c (.ofAdd v)} : Set Y))

@[expose] def K7Sp6Weight3 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], ∀ f : ℕ, 2 ≤ f → IsLie811 Y .psp6 2 f →
    ∀ A : Subgroup Y, IsElemAbelian 3 A → Nat.card A = 27 →
    ∀ c, IsSignedCoords A c → ∀ v : Fin 3 → ZMod 3, (∀ i, v i ≠ 0) →
      ∃ K : Subgroup Y, K ≤ centralizer ({c (.ofAdd v)} : Set Y) ∧ IsQuasisimple ↥K ∧
        3 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K)

@[expose] def Sp6SylowWreath : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], ∀ f : ℕ, IsLie811 Y .psp6 2 f →
    ∀ P : Sylow 3 Y, ∃ n : ℕ, 1 ≤ n ∧
      Nonempty (↥(P : Subgroup Y) ≃* (Multiplicative (ZMod (3 ^ n)) ≀ᵣ Multiplicative (ZMod 3)))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
