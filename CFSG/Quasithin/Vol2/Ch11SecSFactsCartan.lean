module

public import CFSG.Quasithin.Vol2.Ch11SecAFactsFlag
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Defs
public import CFSG.Quasithin.Vol2.Ch11SecAFacts
public import CFSG.Quasithin.Vol2.Ch1Xi

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint SecA
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)

section Vocabulary

variable {W : Type*} [Group W]

abbrev gammaW (H : Subgroup (MulAut W)) (U : Subgroup W) : Subgroup (MulAut W) :=
  perfectCore (H ⊓ stabW U)

abbrev centW (D Γ : Subgroup (MulAut W)) : Subgroup (MulAut W) :=
  D ⊓ sectionCentralizer Γ (pCoreOf 2 Γ)

@[expose] def CartanConcl (H : Subgroup (MulAut W)) (U₁ U₂ : Subgroup W)
    (D : Subgroup (MulAut W)) (q : ℕ) : Prop :=
  D ≤ centW D (gammaW H U₁) ⊔ (D ⊓ gammaW H U₁) ∧
  D ≤ (D ⊓ gammaW H U₁) ⊔ (D ⊓ gammaW H U₂) ∧
  D ⊓ gammaW H U₁ ⊓ sectionCentralizer (gammaW H U₂) (pCoreOf 2 (gammaW H U₂)) = ⊥ ∧
  Nat.card ↥(D ⊓ gammaW H U₁) = q - 1 ∧ Nat.card ↥(centW D (gammaW H U₁)) = q - 1 ∧
  Nat.card ↥(D ⊓ gammaW H U₂) = q - 1 ∧ Nat.card ↥(centW D (gammaW H U₂)) = q - 1

@[expose] def FourDiag (H : Subgroup (MulAut W)) (U₁ U₂ : Subgroup W) (D : Subgroup (MulAut W)) :
    Prop :=
  D ⊓ gammaW H U₁ ≠ centW D (gammaW H U₁) ∧ D ⊓ gammaW H U₁ ≠ D ⊓ gammaW H U₂ ∧
  D ⊓ gammaW H U₁ ≠ centW D (gammaW H U₂) ∧ centW D (gammaW H U₁) ≠ D ⊓ gammaW H U₂ ∧
  centW D (gammaW H U₁) ≠ centW D (gammaW H U₂) ∧ D ⊓ gammaW H U₂ ≠ centW D (gammaW H U₂) ∧
  ∀ E : Subgroup (MulAut W), E ≤ D → Nat.card ↥E = 3 →
    E = D ⊓ gammaW H U₁ ∨ E = centW D (gammaW H U₁) ∨ E = D ⊓ gammaW H U₂ ∨
      E = centW D (gammaW H U₂)

end Vocabulary

@[expose] def FactCartanSL3 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W) (π : ↥(StatedSL 3 K) →* ↥H),
      (FFModel.nat (StatedSL 3 K)).RealizesVia H ⊤ Z π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U₁ U₂ : Subgroup W, IsFlagW H P Z (2 ^ n) 1 U₁ → IsFlagW H P Z (2 ^ n) 2 U₂ →
      ∀ D : Subgroup (MulAut W),
        QuasithinUnique.Lin2.IsHallTwoPrimeOf D (H ⊓ Subgroup.normalizer (P : Set (MulAut W))) →
          CartanConcl H U₁ U₂ D (2 ^ n)

@[expose] def FactCartanSp4 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W) (π : ↥(StatedSp 2 K) →* ↥H),
      (FFModel.nat (StatedSp 2 K)).RealizesVia H ⊤ Z π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U₁ U₂ : Subgroup W, IsFlagW H P Z (2 ^ n) 1 U₁ → IsFlagW H P Z (2 ^ n) 2 U₂ →
      ∀ D : Subgroup (MulAut W),
        QuasithinUnique.Lin2.IsHallTwoPrimeOf D (H ⊓ Subgroup.normalizer (P : Set (MulAut W))) →
          CartanConcl H U₁ U₂ D (2 ^ n) ∧ (n = 2 → FourDiag H U₁ U₂ D)

@[expose] def FactCartanG2 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W)
      (π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H),
      (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).RealizesVia H ⊤ Z π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U₁ U₂ : Subgroup W, IsFlagW H P Z (2 ^ n) 1 U₁ → IsFlagW H P Z (2 ^ n) 2 U₂ →
      ∀ D : Subgroup (MulAut W),
        QuasithinUnique.Lin2.IsHallTwoPrimeOf D (H ⊓ Subgroup.normalizer (P : Set (MulAut W))) →
          CartanConcl H U₁ U₂ D (2 ^ n) ∧ (n = 2 → centW D (gammaW H U₁) ≤ gammaW H U₂)

structure CartanFacts : Prop where
  sl3 : FactCartanSL3
  sp4 : FactCartanSp4
  g2 : FactCartanG2

end CFSG.Quasithin.Vol2.Ch11.SecS
