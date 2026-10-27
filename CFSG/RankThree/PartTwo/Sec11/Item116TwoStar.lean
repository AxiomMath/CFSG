module

public import CFSG.RankThree.PartTwo.Sec11.Item116ResidueT
public import CFSG.RankThree.Theta.TwoPlaneCriterion
public import CFSG.RankThree.PartTwo.Sec11.Item116FusionCases

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.Theta

section Glue

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d : G}

theorem ResidueConfig.mem_partTwoE (h : ResidueConfig G A c L a R Y d) : A ∈ partTwoE G := by
  rw [h.partTwoE_eq h.card_eq]
  exact h.mem_partTwoF

theorem ResidueConfig.d_mem (h : ResidueConfig G A c L a R Y d) : d ∈ A :=
  (show d ∈ A ⊓ L by rw [h.inf_eq_zpowers]; exact Subgroup.mem_zpowers d).1

theorem ResidueConfig.closure_le (h : ResidueConfig G A c L a R Y d) :
    Subgroup.closure ({c, d} : Set G) ≤ A := by
  rw [Subgroup.closure_le]
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl
  · exact h.mem_A
  · exact h.d_mem

theorem ResidueConfig.card_closure (h : ResidueConfig G A c L a R Y d) :
    Nat.card (Subgroup.closure ({c, d} : Set G)) = 9 := by
  have hAe := h.mem_partTwoF.1
  exact Item116Fusion.card_closure_pair_eq_nine hAe.2
    (fun u hu v hv => congrArg Subtype.val (hAe.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)) h.mem_A
    h.d_mem h.ne_one h.not_mem_zpowers

theorem mem_partTwoT_of_twoStar (h : ResidueConfig G A c L a R Y d)
    (hstar : ∀ x ∈ A, x ≠ 1 → TwoStarConditionAt A x)
    (hβ : twoAlpha (Subgroup.closure ({c, d} : Set G)) ≠ ⊥) : A ∈ partTwoT G :=
  two_alpha_criterion h.mem_partTwoE hstar h.closure_le h.card_closure hβ

end Glue

end CFSG.RankThree.PartTwo.Sec11
