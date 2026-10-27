module

public import CFSG.Quasithin.Vol2.Ch11SecA11Concl
public import CFSG.Quasithin.Vol2.Ch11SecSFacts

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint SecS
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)

@[expose] def FactModules3n : Prop :=
  ∀ (K₀ : Type) [Group K₀] [Finite K₀] (W : Type) [CommGroup W] [Finite W],
    (∀ w : W, w ^ 2 = 1) → ∀ (ρ : K₀ →* MulAut W) (n : ℕ), 2 ≤ n →
    Nat.card W ≤ 2 ^ (3 * n) → ⁅(⊤ : Subgroup K₀), (⊤ : Subgroup K₀)⁆ = ⊤ →
    Concl1111 (K₀ ⧸ CFSG.pCore 2 K₀) n → ρ ≠ 1 →
      (∀ S B : Subgroup K₀, QuasithinUnique.IsSylowTwoOf S ⊤ →
        S ≤ Subgroup.normalizer (B : Set K₀) → ⁅B, B⁆ = B →
        (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
          Nonempty (↥B ⧸ CFSG.pCore 2 ↥B ≃* Matrix.SpecialLinearGroup (Fin 2) F)) →
        ∃ r ∈ pCoreOf 2 B, ρ r ≠ 1) ∨
      (n = 2 ∧ (IsAlt 7 (K₀ ⧸ CFSG.pCore 2 K₀) ∨
          IsHat (K₀ ⧸ CFSG.pCore 2 K₀) (alternatingGroup (Fin 7))) ∧
        ∀ y : K₀, (QuotientGroup.mk y : K₀ ⧸ CFSG.pCore 2 K₀) ∈
          Subgroup.center (K₀ ⧸ CFSG.pCore 2 K₀) → Odd (orderOf y) → ρ y = 1) ∨
      (n = 2 ∧ ¬ CFSG.IsQuasisimple (K₀ ⧸ CFSG.pCore 2 K₀) ∧
        ∀ y : K₀, (QuotientGroup.mk y : K₀ ⧸ CFSG.pCore 2 K₀) ∈
          CFSG.fittingSubgroup (K₀ ⧸ CFSG.pCore 2 K₀) → Odd (orderOf y) → ρ y = 1)

@[expose] def FactA7Cent : Prop :=
  ∀ (X : Type) [Group X] [Finite X], (IsAlt 7 X ∨ IsHat X (alternatingGroup (Fin 7))) →
    (∀ B : Subgroup X,
      (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
        Nonempty (↥B ⧸ CFSG.pCore 2 ↥B ≃* Matrix.SpecialLinearGroup (Fin 2) F)) →
      ∀ x : X, orderOf x = 3 → x ∈ sectionCentralizer B (pCoreOf 2 B) →
        x ∈ Subgroup.center X) ∧
    (∀ (s : Bool) (q : ℕ), ¬ IsSLEps3 s q X) ∧ ∀ (s : Bool) (p e : ℕ), ¬ IsPSLEps3 s p e X

section Vocabulary

variable {W : Type*} [Group W]

@[expose] def CartanLine (Z U₂ : Subgroup W) (D : Subgroup (MulAut W)) : Prop :=
  ∀ d ∈ D, (∀ u ∈ U₂, d u * u⁻¹ ∈ Z) → d = 1

end Vocabulary

@[expose] def FactCartanLineSL3 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W) (π : ↥(StatedSL 3 K) →* ↥H),
      (FFModel.nat (StatedSL 3 K)).RealizesVia H ⊤ Z π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U₂ : Subgroup W, IsFlagW H P Z (2 ^ n) 2 U₂ →
      ∀ D : Subgroup (MulAut W),
        QuasithinUnique.Lin2.IsHallTwoPrimeOf D (H ⊓ Subgroup.normalizer (P : Set (MulAut W))) →
          CartanLine Z U₂ D

@[expose] def FactCartanLineSp4 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W) (π : ↥(StatedSp 2 K) →* ↥H),
      (FFModel.nat (StatedSp 2 K)).RealizesVia H ⊤ Z π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U₂ : Subgroup W, IsFlagW H P Z (2 ^ n) 2 U₂ →
      ∀ D : Subgroup (MulAut W),
        QuasithinUnique.Lin2.IsHallTwoPrimeOf D (H ⊓ Subgroup.normalizer (P : Set (MulAut W))) →
          CartanLine Z U₂ D

@[expose] def FactCartanLineG2 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W)
      (π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H),
      (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).RealizesVia H ⊤ Z π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U₂ : Subgroup W, IsFlagW H P Z (2 ^ n) 2 U₂ →
      ∀ D : Subgroup (MulAut W),
        QuasithinUnique.Lin2.IsHallTwoPrimeOf D (H ⊓ Subgroup.normalizer (P : Set (MulAut W))) →
          CartanLine Z U₂ D

@[expose] def FactNoOverlap : Prop :=
  ∀ (X : Type) [Group X] [Finite X],
    (IsPSL 3 2 2 X ∨ (∃ p : ℕ, p.Prime ∧ 11 ≤ p ∧ IsPSL 2 p 1 X) ∨
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
        Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 2) F)) →
    (∀ r : ℕ, r.Prime → r ≠ 2 → ¬ IsSL3 r X ∧ ¬ IsPSL 3 r 1 X) ∧
    (∀ m : ℕ, ¬ IsPSp4 2 m X) ∧ ¬ IsSporadic .M11 X ∧ ¬ IsPSL 4 2 1 X ∧ ¬ IsPSL 5 2 1 X

structure Facts12c : Prop where
  modules : FactModules3n
  a7 : FactA7Cent
  lineSL3 : FactCartanLineSL3
  lineSp4 : FactCartanLineSp4
  lineG2 : FactCartanLineG2
  noOverlap : FactNoOverlap

end CFSG.Quasithin.Vol2.Ch11.SecA
