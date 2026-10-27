module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection5.theorem_5_3

namespace CFSG
end CFSG
open CFSG

/-! # Theorem 5.3(a) from BG Section 5 -/

public theorem CFSG.theorem_5_3_a
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {R : Type*} [Group R] [Finite R] (hnarrow : IsNarrowPGroup p R) (hR : 3 ≤ groupRank R)
    {E : Subgroup R} (hE : E ∈ elementaryAbelianSubgroupsOfRank p 2 R)
    (hEmax : E ∈ maximalElementaryAbelianSubgroups p R) :
    ¬ E ≤ CΩ₁Z₂ p R := by
  exact lemma_5_2_a (p := p) hpodd (R := R) hnarrow.1 hR hE hEmax
