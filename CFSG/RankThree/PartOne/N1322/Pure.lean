module

public import CFSG.RankThree.PartOne.N1322.CoreDefs
public import CFSG.RankThree.SubgroupLists.OrthogonalForms
public import CFSG.RepresentationTheory.UniqueVectorOrbitTwisting
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.RankThree.PartOne.N1322

open scoped Matrix
open CFSG.RepresentationTheory
open CFSG.RankThree.SubgroupLists (omegaGL)

@[expose] def KF1322OmegaList : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p →
    ∀ (X : Subgroup (GL (Fin 3) (ZMod p))) (D : Set (GL (Fin 3) (ZMod p))),
      (∀ g ∈ D, IsRefl g) → X = Subgroup.closure D → (∀ x ∈ X, ∀ g ∈ D, x * g * x⁻¹ ∈ D) →
      (∀ s ∈ D, ∀ t ∈ D, Odd (orderOf (s * t)) → orderOf (s * t) = 1 ∨ orderOf (s * t) = 3) →
      ∀ H : Subgroup (GL (Fin 3) (ZMod p)), H ≤ X → (∀ g ∈ X, ∀ x ∈ H, g * x * g⁻¹ ∈ H) →
        IsIrreducibleMatrixRep H.subtype →
        ∀ M : Matrix (Fin 3) (Fin 3) (ZMod p), Mᵀ = M → M.det ≠ 0 → H = omegaGL M →
          (∀ s ∈ D, ∀ t ∈ D, orderOf (s * t) ≤ 3) ∨ Nonempty (H ≃* GL (Fin 3) (ZMod 2))

@[expose] def KF1322ThreeA6Norm : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ H : Subgroup (GL (Fin 3) (ZMod p)),
    IsIrreducibleMatrixRep H.subtype → Group.IsPerfect H → Nat.card (Subgroup.center H) = 3 →
    Nonempty ((H ⧸ Subgroup.center H) ≃* alternatingGroup (Fin 6)) →
    ∀ g : GL (Fin 3) (ZMod p), (∀ x ∈ H, g * x * g⁻¹ ∈ H) →
      ∃ h ∈ H, ∃ z : GL (Fin 3) (ZMod p), (∀ y : GL (Fin 3) (ZMod p), z * y = y * z) ∧ g = h * z

end CFSG.RankThree.PartOne.N1322
