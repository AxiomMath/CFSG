module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.proposition_10_14_a

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# Proposition 10.14(b) from BG Section 10

This file contains Proposition 10.14(b) from BG Section 10.
-/

section Section10

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

/-- Proposition 10.14(b). -/
public theorem CFSG.proposition_10_14_b
    {p : Nat.Primes} (hpβG : section10IdealPrime p G) :
    ∀ {R : Subgroup G}, IsPGroup p.val R → 1 < groupRank R →
      R ∈ section9UniqueSubgroups G := by
  intro R hRp hRrank_gt
  haveI : Fact p.val.Prime := ⟨p.property⟩
  have hRrank : 2 ≤ groupRank R := Nat.succ_le_of_lt hRrank_gt
  obtain ⟨A, hAR, hArankTwo⟩ :=
    section10_exists_elementaryAbelian_rank_two_subgroup_of_pgroup_rank_two
      (G := G) (p := p.val) hRp hRrank
  have hAnonmax : A ∉ maximalElementaryAbelianSubgroups p.val G := by
    intro hAmax
    have hAin :
        A ∈ section10RankTwoMaximalElementaryAbelianSubgroups p G :=
      ⟨hArankTwo, hAmax⟩
    have hEmpty : section10RankTwoMaximalElementaryAbelianSubgroups p G = ∅ :=
      section10_proposition_10_14_a_ambient (G := G) hpβG
    simp [hEmpty] at hAin
  have hAunique : A ∈ section9UniqueSubgroups G :=
    theorem_9_6_in_particular (G := G)
      ⟨p.val, p.property, hArankTwo, hAnonmax⟩
  exact section9_unique_of_le hAR
    (section10_pSubgroup_proper_of_min_ce (G := G) (p := p.val) hRp) hAunique

end Section10
