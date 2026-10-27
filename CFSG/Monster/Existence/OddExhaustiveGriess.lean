module

public import CFSG.Monster.Existence.TwoPoint.OddTypeDvd
public import CFSG.Monster.Existence.BabyFi22SliceOf
public import CFSG.Monster.Existence.MilestoneInputs
public import CFSG.Monster.GMS.CommonNbr
public import CFSG.Monster.GMS.EdgeSqCo1
public import CFSG.Monster.GMS.EdgeSqReduce
public import CFSG.Monster.GMS.FourAOdd
public import CFSG.Monster.GMS.LeechOddFiveA

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster.GMS CFSG.Blueprint.NativeSporadic

theorem oddExhaustive_MGriess_of
    (I : GMSInterfaces (phiB uBar) MGriess)
    (hLO : LineOddOrder tGriess) : OddExhaustive tGriess xGriess := by
  have hG := gmsF1Type_MGriess_uncond
  have hE1 : EightOneOddOrder tGriess xGriess := U6Odd.eightOneOddOrder_of I hG
  exact s372_mem_oddNbr I hG (commonNbrTwoB_of I hG (babyFi22Slice_of babyTableIII))
    (edgeSquares_of_fact I hG EdgeSq.co1EdgeFact) (eightCentOrders_of I hG) hE1
    (fourAOddOrder_of_eightOne I hG hE1) hLO
    (oddTypeDvd_MGriess I CFSG.Sporadic.Presentation.Th.finite_card_le
      CFSG.Monster.Existence.Compat.card_nativeTh exists_hn_two_point')
    (fiveAInvolutions_of I hG).fiveATwoA

end CFSG.Monster.Existence
