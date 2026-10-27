module

public import CFSG.Monster.Existence.EbCase2
public import CFSG.Monster.Existence.ELevelFullness

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.VisQuot

theorem hEb_FE
    (hcen : CosetTwoBCensus) :
    ∀ e ∈ Subgroup.centralizer (FE : Set MGriess) ⊓
        Subgroup.centralizer ({xGriess} : Set MGriess),
      e * e = 1 → e ∉ FE → ∃ f ∈ FE, IsConj xGriess (e * f) := by
  intro e he hee heF
  by_cases hπ : piVis ⟨(e : SpaceB ≃ₗ[ℚ] SpaceB), mem_Gvis_of_mem_cent_xGriess he.2⟩ = 1
  · exact eb_case_one he hee heF hπ
  · exact eb_case_two hcen he hee hπ

theorem centralizer_FE_le_GmatGriess_of_census
    (hcensus : ∀ y ∈ GmatGriess, IsConj xGriess y → ∃ g ∈ GmatGriess, g * xGriess * g⁻¹ = y)
    (hcen : CosetTwoBCensus) : Subgroup.centralizer (FE : Set MGriess) ≤ GmatGriess :=
  centralizer_FE_le_GmatGriess hcensus (hEb_FE hcen)

end CFSG.Monster.Existence
