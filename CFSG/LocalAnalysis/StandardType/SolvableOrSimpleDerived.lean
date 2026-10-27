module

public import CFSG.LocalAnalysis.StandardType.SylowOvergroupReduction

public section

namespace CFSG.StandardType.SylowOvergroup

@[expose] def SolvableOrSimpleDerived (m : ℕ) (A : Type) [Group A] : Prop :=
  Group.IsSolvable A ∨ (IsSimpleGroup ↥(commutator A) ∧ Nat.card ↥(commutator A) = m)

theorem SolvableOrSimpleDerived.of_mulEquiv {m : ℕ} {A B : Type} [Group A] [Group B]
    (e : A ≃* B) (h : SolvableOrSimpleDerived m A) : SolvableOrSimpleDerived m B := by
  rcases h with h | ⟨hs, hc⟩
  · exact Or.inl (isSolvable_of_mulEquiv e.symm h)
  · refine Or.inr ⟨?_, ?_⟩
    · haveI := hs
      exact (commutatorEquiv e).symm.isSimpleGroup
    · rw [← Nat.card_congr (commutatorEquiv e).toEquiv]
      exact hc

theorem SolvableOrSimpleDerived.of_isSolvable {m : ℕ} {A : Type} [Group A]
    (h : Group.IsSolvable A) : SolvableOrSimpleDerived m A :=
  Or.inl h

theorem SolvableOrSimpleDerived.of_simple_perfect {m : ℕ} {A : Type} [Group A] [IsSimpleGroup A]
    (hp : commutator A = ⊤) (hc : Nat.card A = m) : SolvableOrSimpleDerived m A := by
  have e : ↥(commutator A) ≃* A := (MulEquiv.subgroupCongr hp).trans Subgroup.topEquiv
  refine Or.inr ⟨e.isSimpleGroup, ?_⟩
  rw [Nat.card_congr e.toEquiv]
  exact hc

end CFSG.StandardType.SylowOvergroup
