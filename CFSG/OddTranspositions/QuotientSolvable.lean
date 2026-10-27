module

public import CFSG.Timmesfeld.Bridge.OddTranspBasic

public section

namespace CFSG.OddTranspositions

variable {G : Type} [Group G] [Finite G]

open CFSG.Timmesfeld.Bridge.OddTransp

theorem isSolvable_of_isSolvable_solvableRadical_quotient [Finite G]
    (h : Group.IsSolvable (G ⧸ CFSG.solvableRadical G)) : Group.IsSolvable G := by
  have hR : Group.IsSolvable (CFSG.solvableRadical G) :=
    CFSG.Timmesfeld.Bridge.OddTransp.isSolvable_solvableRadical
  refine Group.isSolvable_of_ker_le_range
    (Subgroup.subtype (CFSG.solvableRadical G))
    (QuotientGroup.mk' (CFSG.solvableRadical G)) ?_
  intro x hx
  rw [QuotientGroup.ker_mk'] at hx
  exact ⟨⟨x, hx⟩, rfl⟩

theorem not_isSolvable_quotient_solvableRadical [Finite G]
    (h : ¬ Group.IsSolvable G) :
    ¬ Group.IsSolvable (G ⧸ CFSG.solvableRadical G) :=
  fun hq => h (isSolvable_of_isSolvable_solvableRadical_quotient hq)

end CFSG.OddTranspositions
