module

public import CFSG.RankThree.PartOne.N1322.CoreData
public import CFSG.RepresentationTheory.UniqueVectorOrbitTwisting
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.RankThree.PartOne.N1322

open CFSG.RepresentationTheory
open scoped Matrix

@[expose] def KAStmt {p : ℕ} [Fact p.Prime] (d : CoreData (ZMod p)) : Prop :=
  d.n = 4 → ∀ g ∈ d.X,
    (¬ ∃ μ : ZMod p, (g : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ d.c = μ • d.c) →
    ∀ t ∈ d.D, ∀ s ∈ d.D, t ∈ d.Lm → s ∈ d.Lm →
    (∀ l ∈ d.Lm, l * t * l⁻¹ ≠ s) → g * t * g⁻¹ ≠ s

@[expose] def KL32Stmt {p : ℕ} [Fact p.Prime] (d : CoreData (ZMod p)) : Prop :=
  ∀ H : Subgroup (GL (Fin 3) (ZMod p)), H ≤ d.X → ∀ _ : ↥H ≃* GL (Fin 3) (ZMod 2),
    (∀ t ∈ d.D, ∃ a ∈ H, a * a = 1 ∧ a ≠ 1 ∧ t = (-1 : GL (Fin 3) (ZMod p)) * a) →
    (∀ a ∈ H, a * a = 1 → a ≠ 1 → (-1 : GL (Fin 3) (ZMod p)) * a ∈ d.D) → False

structure CoreHyp {p : ℕ} [Fact p.Prime] (d : CoreData (ZMod p)) : Prop extends MonoHyp d where
  p5 : 5 ≤ p
  irr : IsIrreducibleMatrixRep d.X.subtype
  noTransv : ∀ g ∈ d.X, ¬ ((((g : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) - 1).rank = 1 ∧
    (((g : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) - 1) *
      (((g : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) - 1) = 0)
  kO : ∀ s ∈ d.D, ∀ t ∈ d.D, Odd (orderOf (s * t)) → orderOf (s * t) = 1 ∨ orderOf (s * t) = 3
  kAL : KAStmt d ∨ KL32Stmt d

end CFSG.RankThree.PartOne.N1322
