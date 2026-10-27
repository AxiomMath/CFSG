module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import CFSG.RankThree.PartOne.KC.PlaneReduction

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.Assembly CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)
open scoped Pointwise

abbrev innSL (n : ℕ) (K : Type) [Field K] : Subgroup (MulAut (projectiveSL n K)) :=
  (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range

@[expose] def PlaneProductIsSubgroup (p : ℕ) {M : Type*} [Group M] (B A : Subgroup M) (t : M) :
    Prop :=
  ((⁅inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer {t}), A⁆ ⊔
      autThetaT p B A : Subgroup M) : Set M) =
    ((⁅inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer {t}), A⁆ : Subgroup M) :
      Set M) * (autThetaT p B A : Set M)

@[expose] def LinearNonsplitInnerPlaneProductsTrivial : Prop :=
  ∀ (p ℓ f n : ℕ) (K : Type) [Field K], p.Prime → 3 < p → ℓ.Prime → ℓ ≠ p → 1 ≤ f → 3 ≤ n →
    Nat.card K = ℓ ^ f → ¬ p ∣ ℓ ^ f - 1 →
    ∀ B : Subgroup (MulAut (projectiveSL n K)), innSL n K ≤ B →
    ∀ E : Subgroup (MulAut (projectiveSL n K)), E ≤ innSL n K → IsElementaryAbelian p E →
      Nat.card E = p ^ 2 →
      (∀ a ∈ E, a ≠ 1 →
        ⁅inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer {a}), E⁆ = ⊥) ∧
      autThetaT p B E = ⊥ ∧ ∀ t ∈ E, t ≠ 1 → autPlaneProduct p B E t = ⊥

@[expose] def NonsplitLinearNoninnerPlaneLocalCoreOdd : Prop :=
  ∀ (p ℓ f n : ℕ) (K : Type) [Field K], p.Prime → 3 < p → ℓ.Prime → ℓ ≠ p → 1 ≤ f → 3 ≤ n →
    Nat.card K = ℓ ^ f → ¬ p ∣ ℓ ^ f - 1 →
    ∀ B : Subgroup (MulAut (projectiveSL n K)), innSL n K ≤ B →
    ∀ A : Subgroup (MulAut (projectiveSL n K)), A ≤ B → IsElementaryAbelian p A →
      Nat.card A = p ^ 2 → ¬ A ≤ innSL n K →
      Nat.card (A ⊓ innSL n K : Subgroup (MulAut (projectiveSL n K))) = p ∧ p ∣ f ∧
      2 ^ p ≤ ℓ ^ f ∧ 3 < ℓ ^ f ∧
      (∀ a ∈ A, a ∉ innSL n K →
        inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer {a}) = ⊥) ∧
      autThetaT p B A = ⊥ ∧
      ∀ t ∈ A, t ≠ 1 →
        PlaneProductIsSubgroup p B A t ∧
        ¬ 2 ∣ Nat.card (autPlaneProduct p B A t) ∧ (t ∉ innSL n K → autPlaneProduct p B A t = ⊥)

@[expose] def LinearBelowPrimeNoninnerPlaneLocalCoreOdd : Prop :=
  ∀ (p ℓ f n : ℕ) (K : Type) [Field K], p.Prime → 3 < p → ℓ.Prime → ℓ ≠ p → 1 ≤ f → 3 ≤ n →
    n < p → Nat.card K = ℓ ^ f →
    ∀ B : Subgroup (MulAut (projectiveSL n K)), innSL n K ≤ B →
    ∀ A : Subgroup (MulAut (projectiveSL n K)), A ≤ B → IsElementaryAbelian p A →
      Nat.card A = p ^ 2 → ¬ A ≤ innSL n K →
      Nat.card (A ⊓ innSL n K : Subgroup (MulAut (projectiveSL n K))) = p ∧ p ∣ f ∧
      (∀ a ∈ A, a ∉ innSL n K →
        inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer {a}) = ⊥) ∧
      autThetaT p B A = ⊥ ∧
      ∀ t ∈ A, t ≠ 1 →
        PlaneProductIsSubgroup p B A t ∧
        ¬ 2 ∣ Nat.card (autPlaneProduct p B A t) ∧ (t ∉ innSL n K → autPlaneProduct p B A t = ⊥)

end CFSG.RankThree.PartOne
