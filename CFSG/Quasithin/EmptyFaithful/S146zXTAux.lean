module

public import CFSG.Quasithin.EmptyFaithful.F918C7

public section

namespace CFSG.Quasithin.S146zX

theorem isSimpleGroup_of_isQuasisimple_of_center_eq_bot {X : Type*} [Group X]
    (hq : CFSG.IsQuasisimple X) (hZ : Subgroup.center X = ⊥) : IsSimpleGroup X := by
  have h : IsSimpleGroup (X ⧸ Subgroup.center X) := hq.2.1
  exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.isSimpleGroup

theorem isSimpleGroup_kbar_of_isQuasisimple {G : Type} [Group G] {L : Subgroup G}
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hZ : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥) : IsSimpleGroup (KBar L) := by
  have h : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
    isSimpleGroup_of_isQuasisimple_of_center_eq_bot hq hZ
  exact (kbarEquiv L).isSimpleGroup

end CFSG.Quasithin.S146zX
