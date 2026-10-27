module

public import CFSG.Quasithin.Vol2.Ch11SecSFacts
public import CFSG.Quasithin.Vol2.Ch11SecSFactsCartan

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint SecS
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)

@[expose] def FactList3Table : Prop :=
  (∀ (X : Type) [Group X] [Finite X],
    (IsAlt 7 X ∨ IsHat X (alternatingGroup (Fin 7)) ∨ IsSporadic .M22 X ∨
      IsHat X (CFSG.Blueprint.NativeSporadic.Carrier .M22) ∨ IsSporadic .M23 X ∨
      IsSporadic .J2 X ∨ IsSporadic .J4 X ∨ IsSporadic .HS X ∨ IsSporadic .Ru X ∨
      IsSLEps3 false 5 X ∨ IsPSLEps3 false 5 1 X) →
    CFSG.IsQuasisimple X ∧ Nat.card (Subgroup.center X) ∣ 3 ∧
      2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) ∧
      ∀ (s : Bool) (p e : ℕ), p.Prime → 1 ≤ e → IsPSLEps3 s p e X →
        s = false ∧ p = 5 ∧ e = 1) ∧
  ∀ (X : Type) [Group X] [Finite X],
    ((∃ p : ℕ, p.Prime ∧ 11 ≤ p ∧ IsPSL 2 p 1 X) ∨ IsPSL 2 5 2 X ∨ IsSLEps3 true 5 X ∨
      IsPSLEps3 true 5 1 X ∨ IsSporadic .J1 X) →
    CFSG.IsQuasisimple X ∧ Subgroup.center X = ⊥ ∧ 3 ∣ Nat.card X

@[expose] def FactCentL2p : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (S : Subgroup Q), S.Normal →
    (∃ p : ℕ, p.Prime ∧ 11 ≤ p ∧ IsPSL 2 p 1 ↥S) →
    ∀ B : Subgroup Q, B ≤ S →
      (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
        Nonempty (↥B ⧸ CFSG.pCore 2 ↥B ≃* Matrix.SpecialLinearGroup (Fin 2) F)) →
      ∀ x : Q, orderOf x = 3 → x ∈ sectionCentralizer B (pCoreOf 2 B) →
        ∀ s ∈ S, x * s = s * x

@[expose] def FactOuterLevi : Prop :=
  ∀ (S : Type) [Group S] [Finite S],
    (IsPSL 2 5 2 S ∨ IsSLEps3 true 5 S ∨ IsPSLEps3 true 5 1 S ∨ IsPSLEps3 false 5 1 S) →
    ∀ R B : Subgroup S, QuasithinUnique.IsSylowTwoOf R ⊤ →
      R ≤ Subgroup.normalizer (B : Set S) → ⁅B, B⁆ = B →
      (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
        Nonempty (↥B ⧸ CFSG.pCore 2 ↥B ≃* Matrix.SpecialLinearGroup (Fin 2) F)) →
      ∃ r ∈ R, ∀ b ∈ B, ∃ y ∈ B, r * y * r⁻¹ * (b * y * b⁻¹)⁻¹ ∉ pCoreOf 2 B

section Vocabulary

variable {W : Type*} [Group W]

@[expose] def FieldAutPoint (H : Subgroup (MulAut W)) (Z U₁ : Subgroup W)
    (D : Subgroup (MulAut W)) : Prop :=
  ∀ τ : MulAut W, (∀ h ∈ H, τ * h * τ⁻¹ ∈ H) → τ ∈ stabW Z → τ ∈ stabW U₁ →
    (∃ k : ℕ, τ ^ 2 ^ k = 1) →
    (∀ γ ∈ gammaW H U₁, ∃ g ∈ gammaW H U₁,
      τ * g * τ⁻¹ * (γ * g * γ⁻¹)⁻¹ ∉ pCoreOf 2 (gammaW H U₁)) →
    ∀ d ∈ centW D (gammaW H U₁), τ * d * τ⁻¹ * d ∈ pCoreOf 2 (H ⊓ stabW U₁)

end Vocabulary

@[expose] def FactFieldAutPointSL3 : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 4 →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W) (π : ↥(StatedSL 3 K) →* ↥H),
      (FFModel.nat (StatedSL 3 K)).RealizesVia H ⊤ Z π → (∀ h ∈ H, ∀ z ∈ Z, h z = z) →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U₁ : Subgroup W, IsFlagW H P Z 4 1 U₁ →
      ∀ D : Subgroup (MulAut W),
        QuasithinUnique.Lin2.IsHallTwoPrimeOf D (H ⊓ Subgroup.normalizer (P : Set (MulAut W))) →
          FieldAutPoint H Z U₁ D

@[expose] def FactFieldAutPointSp4 : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 4 →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W) (π : ↥(StatedSp 2 K) →* ↥H),
      (FFModel.nat (StatedSp 2 K)).RealizesVia H ⊤ Z π → (∀ h ∈ H, ∀ z ∈ Z, h z = z) →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U₁ : Subgroup W, IsFlagW H P Z 4 1 U₁ →
      ∀ D : Subgroup (MulAut W),
        QuasithinUnique.Lin2.IsHallTwoPrimeOf D (H ⊓ Subgroup.normalizer (P : Set (MulAut W))) →
          FieldAutPoint H Z U₁ D

@[expose] def FactFieldAutPointG2 : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 4 →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W)
      (π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H),
      (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).RealizesVia H ⊤ Z π →
      (∀ h ∈ H, ∀ z ∈ Z, h z = z) →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U₁ : Subgroup W, IsFlagW H P Z 4 1 U₁ →
      ∀ D : Subgroup (MulAut W),
        QuasithinUnique.Lin2.IsHallTwoPrimeOf D (H ⊓ Subgroup.normalizer (P : Set (MulAut W))) →
          FieldAutPoint H Z U₁ D

@[expose] def FactJ1 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (S U B : Subgroup Q), S.Normal → IsSporadic .J1 ↥S →
    QuasithinUnique.IsSylowTwoOf U ⊤ → B ≤ S → B ≠ ⊥ → ⁅B, B⁆ = B →
    U ≤ Subgroup.normalizer (B : Set Q) → S ≤ B ⊔ Subgroup.normalizer (U : Set Q)

@[expose] def FactSL34Center : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 4 →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W) (π : ↥(StatedSL 3 K) →* ↥H),
      (FFModel.nat (StatedSL 3 K)).RealizesVia H ⊤ Z π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U₁ : Subgroup W, IsFlagW H P Z 4 1 U₁ →
      ∀ D : Subgroup (MulAut W),
        QuasithinUnique.Lin2.IsHallTwoPrimeOf D (H ⊓ Subgroup.normalizer (P : Set (MulAut W))) →
          (∀ d ∈ centW D (gammaW H U₁), ∀ h ∈ H, d * h = h * d) ∧
          ∀ d ∈ centW D (gammaW H U₁), d ≠ 1 → ∀ w : W, d w = w → w ∈ Z

structure Facts12b : Prop where
  list3 : FactList3Table
  centL2p : FactCentL2p
  outer : FactOuterLevi
  fieldSL3 : FactFieldAutPointSL3
  fieldSp4 : FactFieldAutPointSp4
  fieldG2 : FactFieldAutPointG2
  j1 : FactJ1
  sl34 : FactSL34Center

end CFSG.Quasithin.Vol2.Ch11.SecA
