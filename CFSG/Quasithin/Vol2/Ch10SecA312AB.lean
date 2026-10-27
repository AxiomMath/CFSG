module

public import CFSG.Quasithin.Background.A3Structure312Defs

public section

namespace CFSG.Quasithin.Vol2.Ch10.A312A

open CFSG.Open CFSG.SectionRank CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def A312Types {X : Type} [Group X] (B : Subgroup X) : Prop :=
  (∃ n : ℕ, 1 < n ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
      Nonempty (ModO2 B ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∨
    Nonempty (ModO2 B ≃* alternatingGroup (Fin 5)) ∨
    Nonempty (ModO2 B ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∨
    ∃ n : ℕ, CFSG.Blueprint.SuzukiModel (ModO2 B) 2 n

@[expose] def A312Lift {X : Type} [Group X] (B V : Subgroup X) : Prop :=
  ∃ (I : Type) (_ : Group I) (_ : Finite I) (π : I →* X), Function.Surjective π ∧
    π.ker ≤ Subgroup.center I ∧ IsPGroup 2 π.ker ∧
    ⁅(⊤ : Subgroup I), (⊤ : Subgroup I)⁆ = ⊤ ∧
    ∃ V₁ : Subgroup I, V₁.map π = V ∧
      Subgroup.normalizer (V₁ : Set I) ≤ Subgroup.normalizer ((B.comap π : Subgroup I) : Set I)

@[expose] def A312Sp4 {X : Type} [Group X] (B : Subgroup X) : Prop :=
  ∃ n : ℕ, 1 < n ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
    Nonempty (X ⧸ Subgroup.center X ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F)) ∧
    Nonempty (ModO2 B ≃* Matrix.SpecialLinearGroup (Fin 2) F)

@[expose] def ZCentConf (X : Type) [Group X] [Finite X] (T B : Subgroup X) : Prop :=
  CFSG.IsQuasisimple X ∧ IsSQTKCat X ∧ CFSG.pCore 2 X = ⊥ ∧ IsSylowTwoOf T ⊤ ∧
    B ∈ lFamily T ∧ B ≠ ⊤ ∧ T ≤ Subgroup.normalizer (B : Set X) ∧ A312Types B ∧
    (∃ z ∈ T, z ≠ 1 ∧ (∀ t ∈ T, z * t = t * z) ∧ ∀ b ∈ B, z * b = b * z) ∧
    ∃ V : Subgroup X, V ≤ B ∧ IsElemAbelian 2 V ∧ B ≤ Subgroup.normalizer (V : Set X) ∧
      ⁅V, B⁆ = V ∧ V ≠ ⊥ ∧ pCoreOf 2 B ≤ Subgroup.centralizer (V : Set X) ∧ A312Lift B V

@[expose] def A312ZCentLie : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T B : Subgroup X), (A312C2 B ⊤ ∨ A312C3 B ⊤) →
    ZCentConf X T B → A312Sp4 B

@[expose] def A312ZCentL45 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T B : Subgroup X), (A312C4 B ⊤ ∨ A312C5 B ⊤) →
    ZCentConf X T B → False

@[expose] def A312ZCentM22 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T B : Subgroup X), A312C12 B ⊤ → ZCentConf X T B → False

@[expose] def A312ZCentM23 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T B : Subgroup X), A312C13 B ⊤ → ZCentConf X T B → False

@[expose] def A312ZCentM24 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T B : Subgroup X), A312C14 B ⊤ → ZCentConf X T B → False

@[expose] def A312ZCentJ4 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T B : Subgroup X), A312C17 B ⊤ → ZCentConf X T B → False

@[expose] def A312ZCentHS : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T B : Subgroup X), A312C18 B ⊤ → ZCentConf X T B → False

@[expose] def A312ZCentRu : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T B : Subgroup X), A312C20 B ⊤ → ZCentConf X T B → False

structure A312ZCentFacts : Prop where
  lie : A312ZCentLie
  l45 : A312ZCentL45
  m22 : A312ZCentM22
  m23 : A312ZCentM23
  m24 : A312ZCentM24
  j4 : A312ZCentJ4
  hs : A312ZCentHS
  ru : A312ZCentRu

end CFSG.Quasithin.Vol2.Ch10.A312A
