module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7DLModelDefs

public section

namespace CFSG.StandardType.HdRo7D

open CFSG.Assembly CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def DFixBlockLeaf : Prop :=
  GGLabelRigidInput →
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2], Nat.card F = 2 →
  ∀ (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (Q : QuadraticForm F V),
    (QuadraticMap.polarBilin Q).Nondegenerate → ∀ ℓ : ℕ, Module.finrank F V = 2 * ℓ → 6 ≤ ℓ →
    ∀ t : ↥(CFSG.RankThree.Classical2.orthDerived Q), t ^ 3 = 1 →
    ∀ C : Subgroup ↥(CFSG.RankThree.Classical2.orthDerived Q),
      IsComponentOf C
        (Subgroup.centralizer ({t} : Set ↥(CFSG.RankThree.Classical2.orthDerived Q))) →
      (∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧
        GGHasLabel lab (↥C ⧸ Subgroup.center ↥C) ∧ (lab.tag = .D ∨ lab.tag = .twD) ∧
        lab.n = 1 ∧ lab.rank + 2 = ℓ) →
      Module.finrank F (LinearMap.ker ((t : V ≃ₗ[F] V).toLinearMap - 1)) = 2 * (ℓ - 2) ∧
        ∀ c ∈ C, ∀ v : V, ((c : ↥(CFSG.RankThree.Classical2.orthDerived Q)) : V ≃ₗ[F] V)
          ((t : V ≃ₗ[F] V) v - v) = (t : V ≃ₗ[F] V) v - v

@[expose] def DPlaneCountLeaf : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2], Nat.card F = 2 →
  ∀ (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (Q : QuadraticForm F V),
    (QuadraticMap.polarBilin Q).Nondegenerate → ∀ ℓ : ℕ, Module.finrank F V = 2 * ℓ → 6 ≤ ℓ →
    ∀ E : Subgroup ↥(CFSG.RankThree.Classical2.orthDerived Q), IsElemAbelian 3 E →
      (∀ g : ↥(CFSG.RankThree.Classical2.orthDerived Q), (∀ e ∈ E, g * e = e * g) → g ^ 3 = 1 →
        g ∈ E) →
    ∀ t ∈ E, Module.finrank F (LinearMap.ker ((t : V ≃ₗ[F] V).toLinearMap - 1)) = 2 * (ℓ - 2) →
    ∀ C : Subgroup ↥(CFSG.RankThree.Classical2.orthDerived Q),
      C ≤ Subgroup.centralizer ({t} : Set ↥(CFSG.RankThree.Classical2.orthDerived Q)) →
      (∀ c ∈ C, ∀ v : V, ((c : ↥(CFSG.RankThree.Classical2.orthDerived Q)) : V ≃ₗ[F] V)
        ((t : V ≃ₗ[F] V) v - v) = (t : V ≃ₗ[F] V) v - v) →
      9 ≤ Nat.card ↥(E ⊓ Subgroup.centralizer (C : Set ↥(CFSG.RankThree.Classical2.orthDerived Q)))

@[expose] def DJBlockOmegaLeaf : Prop :=
  GGLabelRigidInput →
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2], Nat.card F = 2 →
  ∀ (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (Q : QuadraticForm F V),
    (QuadraticMap.polarBilin Q).Nondegenerate → ∀ ℓ : ℕ, Module.finrank F V = 2 * ℓ → 6 ≤ ℓ →
    ∀ E : Subgroup ↥(CFSG.RankThree.Classical2.orthDerived Q), IsElemAbelian 3 E →
      (∀ g : ↥(CFSG.RankThree.Classical2.orthDerived Q), (∀ e ∈ E, g * e = e * g) → g ^ 3 = 1 →
        g ∈ E) →
    ∀ t ∈ E, ∀ C : Subgroup ↥(CFSG.RankThree.Classical2.orthDerived Q),
      IsComponentOf C
        (Subgroup.centralizer ({t} : Set ↥(CFSG.RankThree.Classical2.orthDerived Q))) →
      (∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧
        GGHasLabel lab (↥C ⧸ Subgroup.center ↥C) ∧ (lab.tag = .D ∨ lab.tag = .twD) ∧
        lab.n = 1 ∧ lab.rank + 2 = ℓ) →
      9 ≤ Nat.card ↥(E ⊓ Subgroup.centralizer (C : Set ↥(CFSG.RankThree.Classical2.orthDerived Q)))

end CFSG.StandardType.HdRo7D
