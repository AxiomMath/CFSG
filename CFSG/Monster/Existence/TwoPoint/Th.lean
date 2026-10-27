module

public import CFSG.Monster.Existence.TwoPoint.ThHom
public import CFSG.Sporadic.Bridge.ThSurj
public import CFSG.Milestones.FAM_Th_simplicity
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

theorem exists_th_two_point
    (hbound : Finite TauCeti.SporadicName.Th.Group ∧
      Nat.card TauCeti.SporadicName.Th.Group ≤ 90745943887872000) :
    ∃ α β w : MGriess, IsConj tGriess α ∧ IsConj tGriess β ∧ orderOf (α * β) = 3 ∧
      IsConj (α * β) threeCRep ∧ IsConj xGriess w ∧ w ∈ cent2 α β ∧
      (∃ e : MGriess, orderOf e = 7 ∧ e ∈ cent2 α β ⊓ cent w) ∧
      ∃ K : Subgroup MGriess, K ≤ cent2 α β ∧
        Nonempty (K ≃* CFSG.Blueprint.NativeSporadic.Th) := by
  obtain ⟨ψ⟩ := CFSG.Sporadic.Bridge.Th.nonempty_mulEquiv_of_card_le hbound.1 hbound.2
  have ψ' : CFSG.Blueprint.NativeSporadic.Th ≃* thP.Group := ψ
  have hs : IsSimpleGroup thP.Group :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Milestones.fam_th_simplicity ψ'.symm
  exact exists_th_two_point_of_equiv ψ' hs

end CFSG.Monster.Existence
