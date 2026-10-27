module

public import CFSG.Monster.Tri.OddTypeOrders
public import CFSG.Monster.Tri.LeechModelClasses
public import CFSG.Sporadic.Th.Max3.Maximal

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster.GMS CFSG.Monster.Griess CFSG.Monster.Generated CFSG.Monster.Tri.Leech
  CFSG.Blueprint.NativeSporadic

theorem thInvolutionCentralizersGenerate :
    ThInvolutionCentralizersGenerate :=
  CFSG.Sporadic.Th.th_sup_centralizer_eq_top

theorem natCard_Th_eq_monsterThOrder :
    Nat.card Th = CFSG.Open.monsterThOrder := by
  rw [Nat.card_congr CFSG.Sporadic.Th.thEquivJ.toEquiv, CFSG.Sporadic.Th.Max3.natCard_J]
  norm_num [CFSG.Open.monsterThOrder]

variable (I : GMSInterfaces (phiB uBar) MGriess) (hex : OddExhaustive tGriess xGriess)
  (hcard : Nat.card MGriess = CFSG.Open.monsterOrder)
  (hCa : Nat.card ↥(Subgroup.centralizer ({tGriess} : Set MGriess)) = twoBabyOrder)
  (hHN : ∃ α β w : MGriess, IsConj tGriess α ∧ IsConj tGriess β ∧ orderOf (α * β) = 5 ∧
    IsConj xGriess w ∧ w ∈ cent2 α β ∧ ∃ K : Subgroup MGriess, K ≤ cent2 α β ∧
      Nonempty (K ≃* HN))

include I hex hcard hCa hHN

theorem threeCGenerated_MGriess :
    ThreeCGenerated tGriess xGriess :=
  threeCGenerated_MGriess_of I hex hcard hCa CFSG.Sporadic.Presentation.Th.finite_card_le
    natCard_Th_eq_monsterThOrder hHN thInvolutionCentralizersGenerate

theorem oddTypeOrdersCF_tStarG :
    OddTypeOrdersCF tStarG xmatG := by
  rw [← tGmat_eq_tStarG, ← xGmat_eq_xmatG]
  exact oddTypeOrdersCF_Gmat hcard (oddTypeOrdersCF_MGriess I hex hcard hCa
    CFSG.Sporadic.Presentation.Th.finite_card_le natCard_Th_eq_monsterThOrder hHN)

theorem threeCGenerated_tStarG :
    ThreeCGenerated tStarG xmatG := by
  rw [← tGmat_eq_tStarG, ← xGmat_eq_xmatG]
  exact threeCGenerated_Gmat hcard (threeCGenerated_MGriess I hex hcard hCa hHN)

end CFSG.Monster.Existence
