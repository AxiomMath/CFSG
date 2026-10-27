module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12b
public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (W3Lem86_1)

variable {G : Type} [Group G] [Finite G]

theorem exists_minCex88_of_not_concl {V H T : Subgroup G} {i : ℕ} (hyp : Hyp88 V H T i)
    (hfail : ¬ (Concl881 V H ∧ Concl882 V H)) :
    ∃ (H' T' : Subgroup G) (i' : ℕ), MinCex88 V H' T' i' := by
  classical
  have hex : ∃ n : ℕ, ∃ (H' T' : Subgroup G) (i' : ℕ), Hyp88 V H' T' i' ∧
      ¬ (Concl881 V H' ∧ Concl882 V H') ∧ Nat.card H' = n :=
    ⟨Nat.card H, H, T, i, hyp, hfail, rfl⟩
  obtain ⟨H', T', i', hH', hf', hn⟩ := Nat.find_spec hex
  refine ⟨H', T', i', ⟨hH', hf', fun H'' T'' i'' hH'' hf'' => ?_⟩⟩
  rw [hn]
  exact Nat.find_min' hex ⟨H'', T'', i'', hH'', hf'', rfl⟩

end CFSG.LocalAnalysis.WeakClosure81

end
