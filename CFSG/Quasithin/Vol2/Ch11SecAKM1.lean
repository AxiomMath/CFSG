module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint

@[expose] def List3Other (X : Type) [Group X] : Prop :=
  (∃ p : ℕ, p.Prime ∧ (p % 5 = 1 ∨ p % 5 = 4) ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧ IsPSL 2 p 1 X) ∨
    IsPSL 2 5 2 X ∨ (∃ s : Bool, IsSLEps3 s 5 X ∨ IsPSLEps3 s 5 1 X) ∨
    IsSporadic .M22 X ∨ IsHat X (CFSG.Blueprint.NativeSporadic.Carrier .M22) ∨
    IsSporadic .M23 X ∨ IsSporadic .J1 X ∨ IsSporadic .J2 X ∨ IsSporadic .J4 X ∨
    IsSporadic .HS X ∨ IsSporadic .Ru X

@[expose] def FactModulesList3Order : Prop :=
  ∀ (X : Type) [Group X] [Finite X], List3Other X →
    ¬ Nat.card (X ⧸ Subgroup.center X) ∣ Nat.card (Matrix.GeneralLinearGroup (Fin 6) (ZMod 2))

@[expose] def FactModulesList2Bang : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 2 ≤ n →
    (IsPSp4 2 n X ∨ IsG2 2 n X ∨ Is2F4 n X ∨ Is3D4 2 n X ∨ (3 ∣ n ∧ Is3D4 2 (n / 3) X)) →
    ¬ Nat.card (X ⧸ Subgroup.center X) ∣
      Nat.card (Matrix.GeneralLinearGroup (Fin (3 * n)) (ZMod 2))

@[expose] def FactHatA7Module : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsHat X (alternatingGroup (Fin 7)) →
    ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) → Nat.card V ≤ 2 ^ 6 →
      ∀ σ : X →* MulAut V, ¬ Function.Injective σ

@[expose] def FactModulesSL3 : Prop :=
  ∀ (K₀ : Type) [Group K₀] [Finite K₀] (W : Type) [CommGroup W] [Finite W],
    (∀ w : W, w ^ 2 = 1) → ∀ (ρ : K₀ →* MulAut W) (n : ℕ), 2 ≤ n →
    Nat.card W ≤ 2 ^ (3 * n) → ⁅(⊤ : Subgroup K₀), (⊤ : Subgroup K₀)⁆ = ⊤ →
    (IsSL3 (2 ^ n) (K₀ ⧸ CFSG.pCore 2 K₀) ∨ IsPSL 3 2 n (K₀ ⧸ CFSG.pCore 2 K₀)) → ρ ≠ 1 →
      ∀ S B : Subgroup K₀, QuasithinUnique.IsSylowTwoOf S ⊤ →
        S ≤ Subgroup.normalizer (B : Set K₀) → ⁅B, B⁆ = B →
        (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
          Nonempty (↥B ⧸ CFSG.pCore 2 ↥B ≃* Matrix.SpecialLinearGroup (Fin 2) F)) →
        ∃ r ∈ pCoreOf 2 B, ρ r ≠ 1

end CFSG.Quasithin.Vol2.Ch11.SecA
