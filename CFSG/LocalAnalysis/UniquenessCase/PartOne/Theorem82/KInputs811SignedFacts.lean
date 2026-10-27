module

public import CFSG.LieType.Universal.Unitary.Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811ModelTransport
public import CFSG.Open.StatedDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.SignedFacts

open CFSG.Open CFSG.LieType.Universal.Unitary Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82 (IsSignedCoords)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.ModelTransport (ModelK6rRank ModelK7Dvd)

@[expose] def minusPi (q : ℕ) : ℕ := if q % 3 = 1 then q - 1 else q + 1

@[expose] def plusPi (q : ℕ) : ℕ := if q % 3 = 1 then q + 1 else q - 1

@[expose] def Sp6K6cFacts : Prop :=
  ∀ (K : Type) [Field K] [Finite K], (3 : K) ≠ 0 →
    ∃ c₀ : Multiplicative (Fin 3 → ZMod 3) →* StatedSp 3 K, IsSignedCoords c₀.range c₀

@[expose] def Omega7K6cFacts : Prop :=
  ∀ (K : Type) [Field K] [Finite K], (2 : K) ≠ 0 → (3 : K) ≠ 0 →
    ∃ c₀ : Multiplicative (Fin 3 → ZMod 3) →* StatedOmega (StatedQuadOdd 3 K),
      IsSignedCoords c₀.range c₀

@[expose] def Omega8MinusK6cFacts : Prop :=
  ∀ (K : Type) [Field K] [Finite K], (3 : K) ≠ 0 → ∀ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
    ∃ c₀ : Multiplicative (Fin 3 → ZMod 3) →* StatedOmega (StatedQuadMinus 4 K b c),
      IsSignedCoords c₀.range c₀

@[expose] def SLK6cFacts (n : ℕ) : Prop :=
  (n = 6 ∨ n = 7) → ∀ (K : Type) [Field K] [Finite K], Nat.card K % 3 = 2 →
    ∃ c₀ : Multiplicative (Fin 3 → ZMod 3) →* StatedSL n K, IsSignedCoords c₀.range c₀

@[expose] def SUK6cFacts (n : ℕ) : Prop :=
  (n = 6 ∨ n = 7) → ∀ (L : Type) [Field L] [Finite L] (σ : L ≃+* L) (q : ℕ),
    (∀ c, σ (σ c) = c) → (∃ c : L, c ≠ 0 ∧ σ c = -c) → (∀ c, σ c = c ^ q) →
    Nat.card L = q ^ 2 → q % 3 = 1 →
    ∃ c₀ : Multiplicative (Fin 3 → ZMod 3) →* SU σ n, IsSignedCoords c₀.range c₀

structure SignedK6cFacts : Prop where
  sp6 : Sp6K6cFacts
  omega7 : Omega7K6cFacts
  omega8m : Omega8MinusK6cFacts
  sl6 : SLK6cFacts 6
  su6 : SUK6cFacts 6
  sl7 : SLK6cFacts 7
  su7 : SUK6cFacts 7

@[expose] def Sp6K6rFacts : Prop :=
  ∀ (K : Type) [Field K] [Finite K], (3 : K) ≠ 0 →
    ∃ c₀ : Multiplicative (Fin 3 → ZMod 3) →* StatedSp 3 K,
      IsSignedCoords c₀.range c₀ ∧
      ∀ r : ℕ, r.Prime → CharP K r → 5 ≤ r → ModelK6rRank c₀ r

@[expose] def Omega7K6rFacts : Prop :=
  ∀ (K : Type) [Field K] [Finite K], (2 : K) ≠ 0 → (3 : K) ≠ 0 →
    ∃ c₀ : Multiplicative (Fin 3 → ZMod 3) →* StatedOmega (StatedQuadOdd 3 K),
      IsSignedCoords c₀.range c₀ ∧
      ∀ r : ℕ, r.Prime → CharP K r → 5 ≤ r → ModelK6rRank c₀ r

@[expose] def Omega8MinusK6rFacts : Prop :=
  ∀ (K : Type) [Field K] [Finite K], (3 : K) ≠ 0 → ∀ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
    ∃ c₀ : Multiplicative (Fin 3 → ZMod 3) →* StatedOmega (StatedQuadMinus 4 K b c),
      IsSignedCoords c₀.range c₀ ∧
      ∀ r : ℕ, r.Prime → CharP K r → 5 ≤ r → ModelK6rRank c₀ r

@[expose] def SLK6rFacts (n : ℕ) : Prop :=
  (n = 6 ∨ n = 7) → ∀ (K : Type) [Field K] [Finite K], Nat.card K % 3 = 2 →
    ∃ c₀ : Multiplicative (Fin 3 → ZMod 3) →* StatedSL n K,
      IsSignedCoords c₀.range c₀ ∧
      ∀ r : ℕ, r.Prime → CharP K r → 5 ≤ r → ModelK6rRank c₀ r

@[expose] def SUK6rFacts (n : ℕ) : Prop :=
  (n = 6 ∨ n = 7) → ∀ (L : Type) [Field L] [Finite L] (σ : L ≃+* L) (q : ℕ),
    (∀ c, σ (σ c) = c) → (∃ c : L, c ≠ 0 ∧ σ c = -c) → (∀ c, σ c = c ^ q) →
    Nat.card L = q ^ 2 → q % 3 = 1 →
    ∃ c₀ : Multiplicative (Fin 3 → ZMod 3) →* SU σ n,
      IsSignedCoords c₀.range c₀ ∧
      ∀ r : ℕ, r.Prime → CharP L r → 5 ≤ r → ModelK6rRank c₀ r

structure SignedK6rFacts : Prop where
  sp6 : Sp6K6rFacts
  omega7 : Omega7K6rFacts
  omega8m : Omega8MinusK6rFacts
  sl6 : SLK6rFacts 6
  su6 : SUK6rFacts 6
  sl7 : SLK6rFacts 7
  su7 : SUK6rFacts 7

@[expose] def Sp6K7Facts : Prop :=
  ∀ (K : Type) [Field K] [Finite K], (3 : K) ≠ 0 →
    ∃ c₀ : Multiplicative (Fin 3 → ZMod 3) →* StatedSp 3 K,
      IsSignedCoords c₀.range c₀ ∧
      (∀ ℓ : ℕ, ℓ.Prime → 5 ≤ ℓ → ℓ ∣ minusPi (Nat.card K) →
        2 ≤ CFSG.Open.pRank ℓ (centralizer (c₀.range : Set (StatedSp 3 K)))) ∧
      (∀ ℓ : ℕ, ℓ.Prime → 5 ≤ ℓ → ℓ ∣ plusPi (Nat.card K) → ModelK7Dvd c₀ ℓ)

@[expose] def Omega7K7Facts : Prop :=
  ∀ (K : Type) [Field K] [Finite K], (2 : K) ≠ 0 → (3 : K) ≠ 0 →
    ∃ c₀ : Multiplicative (Fin 3 → ZMod 3) →* StatedOmega (StatedQuadOdd 3 K),
      IsSignedCoords c₀.range c₀ ∧
      (∀ ℓ : ℕ, ℓ.Prime → 5 ≤ ℓ → ℓ ∣ minusPi (Nat.card K) →
        2 ≤ CFSG.Open.pRank ℓ
          (centralizer (c₀.range : Set (StatedOmega (StatedQuadOdd 3 K))))) ∧
      (∀ ℓ : ℕ, ℓ.Prime → 5 ≤ ℓ → ℓ ∣ plusPi (Nat.card K) → ModelK7Dvd c₀ ℓ)

@[expose] def Omega8MinusK7Facts : Prop :=
  ∀ (K : Type) [Field K] [Finite K], (3 : K) ≠ 0 → ∀ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
    ∃ c₀ : Multiplicative (Fin 3 → ZMod 3) →* StatedOmega (StatedQuadMinus 4 K b c),
      IsSignedCoords c₀.range c₀ ∧
      (∀ ℓ : ℕ, ℓ.Prime → 5 ≤ ℓ → ℓ ∣ minusPi (Nat.card K) →
        2 ≤ CFSG.Open.pRank ℓ
          (centralizer (c₀.range : Set (StatedOmega (StatedQuadMinus 4 K b c)))))

@[expose] def SLK7Facts (n : ℕ) : Prop :=
  (n = 6 ∨ n = 7) → ∀ (K : Type) [Field K] [Finite K], Nat.card K % 3 = 2 →
    ∃ c₀ : Multiplicative (Fin 3 → ZMod 3) →* StatedSL n K,
      IsSignedCoords c₀.range c₀ ∧
      (∀ ℓ : ℕ, ℓ.Prime → 5 ≤ ℓ → ℓ ∣ Nat.card K + 1 →
        2 ≤ CFSG.Open.pRank ℓ (centralizer (c₀.range : Set (StatedSL n K)))) ∧
      (∀ ℓ : ℕ, ℓ.Prime → 5 ≤ ℓ → ℓ ∣ Nat.card K - 1 →
        2 ≤ CFSG.Open.pRank ℓ (centralizer (c₀.range : Set (StatedSL n K))) ∧
        (n = 7 → 3 ≤ CFSG.Open.pRank ℓ (centralizer (c₀.range : Set (StatedSL n K)))))

@[expose] def SUK7Facts (n : ℕ) : Prop :=
  (n = 6 ∨ n = 7) → ∀ (L : Type) [Field L] [Finite L] (σ : L ≃+* L) (q : ℕ),
    (∀ c, σ (σ c) = c) → (∃ c : L, c ≠ 0 ∧ σ c = -c) → (∀ c, σ c = c ^ q) →
    Nat.card L = q ^ 2 → q % 3 = 1 →
    ∃ c₀ : Multiplicative (Fin 3 → ZMod 3) →* SU σ n,
      IsSignedCoords c₀.range c₀ ∧
      (∀ ℓ : ℕ, ℓ.Prime → 5 ≤ ℓ → ℓ ∣ q - 1 →
        2 ≤ CFSG.Open.pRank ℓ (centralizer (c₀.range : Set (SU σ n)))) ∧
      (∀ ℓ : ℕ, ℓ.Prime → 5 ≤ ℓ → ℓ ∣ q + 1 →
        2 ≤ CFSG.Open.pRank ℓ (centralizer (c₀.range : Set (SU σ n))) ∧
        (n = 7 → 3 ≤ CFSG.Open.pRank ℓ (centralizer (c₀.range : Set (SU σ n)))))

structure SignedK7Facts : Prop where
  sp6 : Sp6K7Facts
  omega7 : Omega7K7Facts
  omega8m : Omega8MinusK7Facts
  sl6 : SLK7Facts 6
  su6 : SUK7Facts 6
  sl7 : SLK7Facts 7
  su7 : SUK7Facts 7

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.SignedFacts
