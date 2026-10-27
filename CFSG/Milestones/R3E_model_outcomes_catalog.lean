module

public import CFSG.Blueprint.RankThreeModels

public section

namespace CFSG.Milestones

open Blueprint

theorem r3e_model_outcomes_catalog (G : Type) [Group G]
    (h : RankThreeIModel G ∨ RankThreeIIModel G) : Catalog G := by
  have classical : ∀ (t : Assembly.LowTwoRank.StatedLieTag) (n p f : ℕ),
      Assembly.LowTwoRank.StatedClassicalModel G t n p f → Catalog G := fun t n p f hm =>
    .inr (.inr (.inl ((fam_classical_model_membership_alltags G).2 ⟨t, n, p, f, hm⟩)))
  rcases h with ⟨f, -, hm | hm | hm | hm⟩ | hm | hm | ⟨x, -, hm⟩ | hm
  · exact classical _ _ _ _ hm
  · exact classical _ _ _ _ hm
  · exact classical _ _ _ _ hm
  · exact classical _ _ _ _ hm
  · exact .inr (.inr (.inr (.inr ⟨.Co2, hm⟩)))
  · exact .inr (.inr (.inr (.inr ⟨.Th, hm⟩)))
  · exact classical _ _ _ _ hm
  · exact .inr (.inr (.inr (.inl (.inl ⟨.F4, 2, 1, by decide, hm⟩))))

end CFSG.Milestones
