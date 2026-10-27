module

public import CFSG.Quasithin.Background.B4ModelsLie
public import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)

section Vocabulary

variable {W : Type*} [Group W]

@[expose] def EndStableW (H : Subgroup (MulAut W)) (Z U : Subgroup W) : Prop :=
  ∀ φ : W →* W, (∀ z ∈ Z, φ z ∈ Z) → (∀ h ∈ H, ∀ w : W, φ (h w) * (h (φ w))⁻¹ ∈ Z) →
    ∀ u ∈ U, φ u ∈ U

@[expose] def stabW (U : Subgroup W) : Subgroup (MulAut W) where
  carrier := {h | ∀ u : W, u ∈ U ↔ h u ∈ U}
  one_mem' := fun _ => Iff.rfl
  mul_mem' := by
    intro a b ha hb u
    rw [MulAut.mul_apply, ← ha (b u), ← hb u]
  inv_mem' := by
    intro a ha u
    have := ha (a⁻¹ u)
    rw [MulAut.apply_inv_self] at this
    exact this.symm

theorem mem_stabW {U : Subgroup W} {h : MulAut W} : h ∈ stabW U ↔ ∀ u : W, u ∈ U ↔ h u ∈ U :=
  Iff.rfl

@[expose] def IsFlagW (H P : Subgroup (MulAut W)) (Z : Subgroup W) (q i : ℕ) (U : Subgroup W) :
    Prop :=
  Z ≤ U ∧ EndStableW H Z U ∧ Z.relIndex U = q ^ i ∧ P ≤ stabW U

@[expose] def HasUniqueFlagW (H P : Subgroup (MulAut W)) (Z : Subgroup W) (q : ℕ) : Prop :=
  ∃ U₁ U₂ U₃ : Subgroup W, IsFlagW H P Z q 1 U₁ ∧ IsFlagW H P Z q 2 U₂ ∧
    IsFlagW H P Z q 3 U₃ ∧ U₁ ≤ U₂ ∧ U₂ ≤ U₃ ∧
    (∀ U, IsFlagW H P Z q 1 U → U = U₁) ∧ (∀ U, IsFlagW H P Z q 2 U → U = U₂) ∧
    (∀ U, IsFlagW H P Z q 3 U → U = U₃)

end Vocabulary

@[expose] def FactFlagSL3 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W) (π : ↥(StatedSL 3 K) →* ↥H),
      (FFModel.nat (StatedSL 3 K)).RealizesVia H ⊤ Z π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H → HasUniqueFlagW H P Z (2 ^ n)

@[expose] def FactFlagSp4 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W) (π : ↥(StatedSp 2 K) →* ↥H),
      (FFModel.nat (StatedSp 2 K)).RealizesVia H ⊤ Z π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H → HasUniqueFlagW H P Z (2 ^ n)

@[expose] def FactFlagG2 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W)
      (π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H),
      (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).RealizesVia H ⊤ Z π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H → HasUniqueFlagW H P Z (2 ^ n)

@[expose] def FactLeviSL3 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W) (π : ↥(StatedSL 3 K) →* ↥H),
      (FFModel.nat (StatedSL 3 K)).RealizesVia H ⊤ Z π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ (i : ℕ) (U : Subgroup W), (i = 1 ∨ i = 2) → IsFlagW H P Z (2 ^ n) i U →
        Nonempty (↥(perfectCore (H ⊓ stabW U)) ⧸ CFSG.pCore 2 ↥(perfectCore (H ⊓ stabW U)) ≃*
          Matrix.SpecialLinearGroup (Fin 2) K)

@[expose] def FactLeviSp4 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W) (π : ↥(StatedSp 2 K) →* ↥H),
      (FFModel.nat (StatedSp 2 K)).RealizesVia H ⊤ Z π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ (i : ℕ) (U : Subgroup W), (i = 1 ∨ i = 2) → IsFlagW H P Z (2 ^ n) i U →
        Nonempty (↥(perfectCore (H ⊓ stabW U)) ⧸ CFSG.pCore 2 ↥(perfectCore (H ⊓ stabW U)) ≃*
          Matrix.SpecialLinearGroup (Fin 2) K)

@[expose] def FactLeviG2 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W)
      (π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H),
      (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).RealizesVia H ⊤ Z π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ (i : ℕ) (U : Subgroup W), (i = 1 ∨ i = 2) → IsFlagW H P Z (2 ^ n) i U →
        Nonempty (↥(perfectCore (H ⊓ stabW U)) ⧸ CFSG.pCore 2 ↥(perfectCore (H ⊓ stabW U)) ≃*
          Matrix.SpecialLinearGroup (Fin 2) K)

@[expose] def FactN13Sp4 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W) (π : ↥(StatedSp 2 K) →* ↥H),
      (FFModel.nat (StatedSp 2 K)).RealizesVia H ⊤ Z π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U₁ U₃ : Subgroup W, IsFlagW H P Z (2 ^ n) 1 U₁ → IsFlagW H P Z (2 ^ n) 3 U₃ →
      ∀ τ : MulAut W, τ ∈ stabW Z → (∀ h ∈ H, τ * h * τ⁻¹ ∈ H) →
        (τ ∈ stabW U₁ ↔ τ ∈ stabW U₃)

@[expose] def FactN13G2 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W)
      (π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H),
      (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).RealizesVia H ⊤ Z π →
      ∀ P : Subgroup (MulAut W), QuasithinUnique.IsSylowTwoOf P H →
      ∀ U₁ U₃ : Subgroup W, IsFlagW H P Z (2 ^ n) 1 U₁ → IsFlagW H P Z (2 ^ n) 3 U₃ →
      ∀ τ : MulAut W, τ ∈ stabW Z → (∀ h ∈ H, τ * h * τ⁻¹ ∈ H) →
        (τ ∈ stabW U₁ ↔ τ ∈ stabW U₃)

structure NatFacts : Prop where
  flagSL3 : FactFlagSL3
  flagSp4 : FactFlagSp4
  flagG2 : FactFlagG2
  leviSL3 : FactLeviSL3
  leviSp4 : FactLeviSp4
  leviG2 : FactLeviG2
  n13Sp4 : FactN13Sp4
  n13G2 : FactN13G2

end CFSG.Quasithin.Vol2.Ch11.SecA
