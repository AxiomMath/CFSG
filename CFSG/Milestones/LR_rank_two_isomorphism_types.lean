module

public import CFSG.LocalAnalysis.RankTwoShapes.IsomorphismTypesFromTheoremBStar
public import CFSG.CharacterTheory.Semidihedral.AllPrimeQDInputs

public section

universe u v w

namespace CFSG.Assembly.LowTwoRank

open Matrix in
theorem _root_.CFSG.Milestones.lr_rank_two_isomorphism_types
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hrank : twoRank G = 2) :
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ StatedClassicalModel G .PSL 2 p f) ∨
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ StatedClassicalModel G .PSL 3 p f) ∨
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ StatedClassicalModel G .PSU 3 p f) ∨
    StatedClassicalModel G .PSU 3 2 2 ∨
    Nonempty (G ≃* alternatingGroup (Fin 7)) ∨
    Nonempty (G ≃* StatedM11) :=
  CFSG.RankTwoShapes.rank_two_isomorphism_types_of_semidihedral_theoremBStar
    CFSG.Semidihedral.AllPrime.stationaryCoverageStatement G hnonab hrank

end CFSG.Assembly.LowTwoRank
