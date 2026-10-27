module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Invariant

import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.Basic

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

section MinimalNormalInvariant

variable {G A : Type*} [Group G] [Finite G] [Group A] [MulDistribMulAction A G]

/-- Existence of a minimal nontrivial normal `A`-invariant subgroup in a finite nontrivial group. -/
public theorem CFSG.exists_minimal_normal_isInvariant [Nontrivial G] :
    ∃ M : Subgroup G,
      M.Normal ∧ IsInvariant A G M ∧ M ≠ ⊥ ∧
        (∀ K : Subgroup G, K.Normal → IsInvariant A G K → K ≠ ⊥ → K ≤ M → K = M) := by
  classical
  -- Work with the predicate expressing "nontrivial, normal, and invariant".
  let P : ℕ → Prop :=
    fun n =>
      ∃ K : Subgroup G, K.Normal ∧ IsInvariant A G K ∧ K ≠ ⊥ ∧ Nat.card K = n
  have hP : ∃ n, P n := by
    refine ⟨Nat.card G, ?_⟩
    refine ⟨⊤, ?_, ?_, ?_, ?_⟩
    · infer_instance
    · -- `⊤` is invariant under any action.
      refine ⟨?_⟩
      intro a g
      simp
    · simp
    · simp
  -- Choose a witness of minimal cardinality.
  let n0 : ℕ := Nat.find hP
  rcases (Nat.find_spec hP) with ⟨M, hMnorm, hMinv, hMne, hcardM⟩
  refine ⟨M, hMnorm, hMinv, hMne, ?_⟩
  intro K hKnorm hKinv hKne hKle
  by_contra hKneM
  -- If `K ≤ M` but `K ≠ M`, then `|K| < |M|` (finite strict inclusion decreases cardinality).
  have hcard_lt : Nat.card K < Nat.card M := by
    have hle : Nat.card K ≤ Nat.card M := Subgroup.card_le_of_le (H := K) (K := M) hKle
    have hne_card : Nat.card K ≠ Nat.card M := by
      intro hEq
      have hge : Nat.card M ≤ Nat.card K := by simp [hEq]
      have : K = M := Subgroup.eq_of_le_of_card_ge (H := K) (K := M) hKle hge
      exact hKneM this
    exact lt_of_le_of_ne hle hne_card
  -- But then `P (Nat.card K)` contradicts minimality of `n0`.
  have hPK : P (Nat.card K) := ⟨K, hKnorm, hKinv, hKne, rfl⟩
  have : ¬ P (Nat.card K) := by
    -- `Nat.card K < n0` since `Nat.card M = n0`.
    have : Nat.card K < n0 := by simpa [n0, hcardM] using hcard_lt
    exact Nat.find_min hP this
  exact this hPK

end MinimalNormalInvariant
