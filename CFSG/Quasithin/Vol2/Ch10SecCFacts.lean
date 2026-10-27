module

public import CFSG.Quasithin.Background.A1cModuleDefs
public import CFSG.Quasithin.Background.B4ModelsLie
public import CFSG.Quasithin.Background.B6Sections
public import CFSG.Quasithin.H13.StatementsFSU

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique
open CFSG.Assembly.LowTwoRank (StatedSp)
open scoped IsMulCommutative

section ModCase

variable {Γ : Type} [Group Γ]

@[expose] def ModCase (L V₁ : Subgroup Γ) : Prop :=
  ∃ _ : IsMulCommutative ↥V₁,
    (∃ n : ℕ, 1 < n ∧ (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
        Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) K)) ∧
      BinaryNaturalSL (V := ↥V₁) (autOn L V₁) ⊤
        ((Subgroup.centralizer (L : Set Γ)).subgroupOf V₁) 2 n) ∨
    (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 5)) ∧
      AlternatingNatural (V := ↥V₁) (autOn L V₁) ⊤ ⊥ 5) ∨
    (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∧
      BinaryNaturalSL (V := ↥V₁) (autOn L V₁) ⊤
        ((Subgroup.centralizer (L : Set Γ)).subgroupOf V₁) 3 1) ∨
    (∃ n : ℕ, 1 < n ∧ (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ (2 * n) ∧
        Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) K)) ∧
      BinaryOrthogonalFour (V := ↥V₁) (autOn L V₁) ⊤ ⊥ n) ∨
    (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∧
      ∃ s ∈ Subgroup.normalizer (L : Set Γ), ∃ W : Subgroup Γ, W ≤ V₁ ∧
        L ≤ Subgroup.normalizer (W : Set Γ) ∧ W ⊔ CFSG.conjugate W s = V₁ ∧
        W ⊓ CFSG.conjugate W s = ⊥ ∧
        (∃ _ : IsMulCommutative ↥W, BinaryNaturalSL (V := ↥W) (autOn L W) ⊤ ⊥ 3 1) ∧
        ¬ IsXSectionIso L ⊥ W (CFSG.conjugate W s)) ∨
    (∃ n : ℕ, CFSG.Blueprint.SuzukiModel (↥L ⧸ CFSG.pCore 2 ↥L) 2 n ∧
      BinaryNaturalSz (V := ↥V₁) (autOn L V₁) ⊤ ⊥ n)

end ModCase

@[expose] def FactK1 : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (H R J L V₁ : Subgroup Γ),
    SQTKGroup ↥H → pCoreOf 2 H ≠ ⊥ → IsSylowTwoOf R H → J ∈ cComp H →
    CFSG.Open.IsQuasisimple ↥J → L ∈ lFamily R → L ≤ J → L ≠ J →
    R ≤ Subgroup.normalizer (L : Set Γ) → IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) →
    V₁ ≤ L → IsElemAbelian 2 V₁ → L ⊔ R ≤ Subgroup.normalizer (V₁ : Set Γ) → ⁅V₁, L⁆ = V₁ →
    pCoreOf 2 L ≤ Subgroup.centralizer (V₁ : Set Γ) →
    J ⊓ Subgroup.normalizer (V₁ : Set Γ) ≤ Subgroup.normalizer (L : Set Γ) → ModCase L V₁ →
    R ⊓ Subgroup.centralizer (L : Set Γ) ≤ Subgroup.centralizer (J : Set Γ) ∨
      ∃ n : ℕ, 1 < n ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
        Nonempty (↥J ⧸ Subgroup.center ↥J ≃* ↥(StatedSp 2 F)) ∧
        Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) F)

@[expose] def FactK3Sp4 : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (H R J L V₁ : Subgroup Γ) (n : ℕ) (F : Type) [Field F]
    [Finite F],
    SQTKGroup ↥H → pCoreOf 2 H ≠ ⊥ → IsSylowTwoOf R H → J ∈ cComp H → L ∈ lFamily R → L ≤ J →
    L ≠ J → R ≤ Subgroup.normalizer (L : Set Γ) → IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) →
    V₁ ≤ L → IsElemAbelian 2 V₁ → L ⊔ R ≤ Subgroup.normalizer (V₁ : Set Γ) → ⁅V₁, L⁆ = V₁ →
    pCoreOf 2 L ≤ Subgroup.centralizer (V₁ : Set Γ) →
    J ⊓ Subgroup.normalizer (V₁ : Set Γ) ≤ Subgroup.normalizer (L : Set Γ) → ModCase L V₁ →
    1 < n → Nat.card F = 2 ^ n → Nonempty (↥J ≃* ↥(StatedSp 2 F)) →
    Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) F) →
    ∃ X : Subgroup Γ, X ≤ J ⊓ Subgroup.normalizer (L : Set Γ) ∧ Nat.card X = 2 ^ n - 1 ∧
      (∀ x ∈ X, ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ V₁) ∧ X ⊓ Subgroup.centralizer (V₁ : Set Γ) = ⊥

@[expose] def FactK8a : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (Hm : Subgroup (MulAut V)) (U Z : Subgroup V) (n : ℕ),
    1 ≤ n → BinaryOrthogonalFour Hm U Z n → XMod.IsIrrSec ↥Hm Z U

@[expose] def FactK8b : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (Hm : Subgroup (MulAut V)) (U Z : Subgroup V) (f : ℕ),
    BinaryNaturalSz Hm U Z f → XMod.IsIrrSec ↥Hm Z U

end CFSG.Quasithin.Vol2.Ch10.SecC
