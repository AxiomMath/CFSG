module

public import CFSG.Blueprint.Catalog
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open CFSG.Blueprint (LieModel)
open scoped Pointwise

@[expose] def L3InvertSplit : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → p ≠ 2 →
    (LieModel X .PSL 3 p 1 ∨ LieModel X .PSU 3 p 1) →
    ∀ A S B : Subgroup (MulAut X), (MulAut.conj : X →* MulAut X).range ≤ A →
      CFSG.ABGLocalTools.IsSylowOf 2 S A → B ≤ A → IsMulCommutative ↥B → Odd (Nat.card B) →
      3 ∣ Nat.card B → 5 ∣ Nat.card B →
      (B : Set (MulAut X)) * (S : Set (MulAut X)) = (S : Set (MulAut X)) * (B : Set (MulAut X)) →
      (∀ K : Subgroup X, ⁅K, K⁆ = K → Nat.card K = p * (p ^ 2 - 1) →
        ∀ d ∈ B, (orderOf d).Prime → (∀ k ∈ K, d k = k) → ∃ a ∈ A, a * d * a⁻¹ = d⁻¹) →
      ∃ s ∈ S, ∀ b ∈ B, s * b * s⁻¹ = b⁻¹

end CFSG.LocalAnalysis.UniquenessCase.UC22
