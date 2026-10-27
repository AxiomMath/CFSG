module

public import CFSG.LocalAnalysis.WeakClosure81.EightDefs
public import CFSG.Quasithin.Background.E3Defs
public import CFSG.Blueprint.Catalog
public import CFSG.Open.StatedDefs
public import CFSG.Open.PGLModelDefs
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.GroupTheory.PCore.Transport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.Quasithin.Background.B2FactorizationOffender
public import CFSG.Quasithin.Background.B2FactorizationR2
public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.Background.B2FactorizationSum
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open Matrix

variable {G : Type*} [Group G]

@[expose] def HasQuotShape (K : Subgroup G) (N : Set G) (P : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∃ (X : Type) (_ : Group X) (φ : ↥K →* X), Function.Surjective φ ∧
    (∀ k : ↥K, φ k = 1 ↔ (k : G) ∈ N) ∧ P X

@[expose] def centerPre (K : Subgroup G) (N : Set G) : Set G :=
  {k | k ∈ K ∧ ∀ x ∈ K, k * x * k⁻¹ * x⁻¹ ∈ N}

@[expose] def IsSymGp (X : Type) [Group X] (m : ℕ) : Prop :=
  Nonempty (X ≃* Equiv.Perm (Fin m))

@[expose] def IsL2Gp (X : Type) [Group X] (n : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
    Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 2) F)

@[expose] def IsSpGp (X : Type) [Group X] (m n : ℕ) : Prop :=
  ∃ k : ℕ, m = 2 * k ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
    Nonempty (X ≃* ↥(StatedSp k F))

@[expose] def IsPSUGp (X : Type) [Group X] (m n : ℕ) : Prop :=
  CFSG.Blueprint.LieModel X .PSU m 2 n

@[expose] def IsOrthPlusGp (X : Type) [Group X] (k n : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
    Nonempty (X ≃* ↥(CFSG.PGLModel.orthogonalPlus k F))

@[expose] def IsOrthMinusGp (X : Type) [Group X] (k n : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
    ∃ b c : F, (∀ s : F, s ^ 2 + b * s + c ≠ 0) ∧
      Nonempty (X ≃* ↥(CFSG.PGLModel.orthogonalMinus k F b c))

@[expose] def IsOrthGp (X : Type) [Group X] (m n : ℕ) : Prop :=
  (∃ k : ℕ, 2 ≤ k ∧ m = 2 * k ∧ IsOrthPlusGp X k n) ∨
    (∃ k : ℕ, 1 ≤ k ∧ m = 2 * k + 2 ∧ IsOrthMinusGp X k n)

@[expose] def wreathAct (L : Type) [Group L] (m : ℕ) :
    Equiv.Perm (Fin m) →* MulAut (Fin m → L) where
  toFun σ := MulEquiv.arrowCongr σ (MulEquiv.refl L)
  map_one' := by
    ext x i
    simp only [MulEquiv.arrowCongr_apply]
    rfl
  map_mul' σ τ := by
    ext x i
    simp only [MulEquiv.arrowCongr_apply]
    rfl

abbrev WreathSym (L : Type) [Group L] (m : ℕ) : Type :=
  (Fin m → L) ⋊[wreathAct L m] Equiv.Perm (Fin m)

@[expose] def IsL2WrSymGp (X : Type) [Group X] (n m : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
    Nonempty (X ≃* WreathSym (Matrix.SpecialLinearGroup (Fin 2) F) m)

@[expose] def IsOrth6MinusMod (Y : Type) [Group Y] : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 3 ∧
    ∃ b c : F, (∀ s : F, s ^ 2 + b * s + c ≠ 0) ∧
      ∃ N : Subgroup (Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F),
        CFSG.PGLModel.projOmegaMinus 2 F b c ≤ N ∧
          N ≤ (CFSG.PGLModel.orthogonalMinus 2 F b c).map Matrix.ProjGenLinGroup.mk ∧
          Nonempty (Y ≃* ↥N)

@[expose] def IsThreeCoverOrth6Minus (X : Type) [Group X] : Prop :=
  ∃ (Y : Type) (_ : Group Y) (φ : X →* Y), Function.Surjective φ ∧ Nat.card φ.ker = 3 ∧
    φ.ker ≤ Subgroup.center X ∧ IsOrth6MinusMod Y

end CFSG.LocalAnalysis.WeakClosure81
