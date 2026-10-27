module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LargeExtraspecial.S9TIInput

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem lt_inf_normalizer_of_isPGroup {p : ℕ} [Fact p.Prime] {S R : Subgroup G}
    (hR : IsPGroup p R) (hSR : S ≤ R) (hne : S ≠ R) : S < R ⊓ normalizer (S : Set G) := by
  haveI : Group.IsNilpotent R := hR.isNilpotent
  have hnc : NormalizerCondition R := Group.normalizerCondition_of_isNilpotent
  have hS' : S.subgroupOf R < ⊤ :=
    lt_top_iff_ne_top.2 fun h => hne (le_antisymm hSR (Subgroup.subgroupOf_eq_top.1 h))
  obtain ⟨x, hxn, hxS'⟩ := SetLike.exists_of_lt (hnc _ hS')
  refine lt_of_le_of_ne (le_inf hSR Subgroup.le_normalizer) fun heq => ?_
  have hx : (x : G) ∈ R ⊓ normalizer (S : Set G) := by
    refine Subgroup.mem_inf.2 ⟨x.2, ?_⟩
    rw [mem_normalizer_iff]
    intro g
    have key := mem_normalizer_iff.1 hxn
    constructor
    · intro hg
      exact (key ⟨g, hSR hg⟩).1 hg
    · intro hg
      have hgR : g ∈ R := by
        have h1 : (x : G)⁻¹ * ((x : G) * g * (x : G)⁻¹) * (x : G) ∈ R :=
          R.mul_mem (R.mul_mem (R.inv_mem x.2) (hSR hg)) x.2
        simpa [mul_assoc] using h1
      exact (key ⟨g, hgR⟩).2 hg
  rw [← heq] at hx
  exact hxS' hx

end CFSG.LocalAnalysis.WeakClosure81
