module

public import CFSG.Monster.GMS.Uniqueness
public import CFSG.Monster.Tri.ASegFactsMain
public import CFSG.Monster.GMS.A12Fi23
public import CFSG.Monster.GMS.BabyReduce
public import CFSG.Monster.GMS.CoTwoAssembly
public import CFSG.Monster.GMS.EdgeSqCo1
public import CFSG.Monster.GMS.EdgeSqReduce
public import CFSG.Monster.GMS.FourAOdd
public import CFSG.Monster.GMS.LeechOddFiveA

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Tri

open CFSG.Monster.GMS CFSG.Blueprint.NativeSporadic CFSG.Monster.B.Recog
  CFSG.Monster.Existence CFSG.Monster.Generated CFSG.Monster.Tri.Leech

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ : G}

theorem ASegFacts.of_parts
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hLO : BabyLineOddOrder) (hFi : BabyFi22Slice) (hOT : OddTypeOrdersCF a z₀) :
    ASegFacts a z₀ := by
  have hCN : CommonNbrTwoB a z₀ := commonNbrTwoB_of I hG hFi
  have hOT' : OddTypeOrders a z₀ := oddTypeOrders_of (threeAFi23_of I hG hFi) hOT
  have hES : EdgeSquares a := edgeSquares_of_fact I hG EdgeSq.co1EdgeFact
  have hF4 : FourAOddOrder a z₀ := fourAOddOrder_of_leech I hG
  have hLO' : LineOddOrder a := lineOddOrder_of I hG hLO
  have hEC : EightCentOrders a z₀ := eightCentOrders_of I hG
  have hE1 : EightOneOddOrder a z₀ := U6Odd.eightOneOddOrder_of I hG
  have hF5 : FiveATwoA a z₀ := (fiveAInvolutions_of I hG).fiveATwoA
  exact { gammaCover := gammaCover_of I hG hCN hES hEC hE1 hF4 hLO' hOT'.toDvd hF5
          linesHaveInvolutions :=
            linesHaveInvolutions_of I hG hCN hES hEC hE1 hF4 hLO' hOT'.toDvd hF5
          commonNbrTwoB := hCN
          oddTypeOrders := hOT'
          eightLines := eightGroupLines_of I hG
          a12 := exists_a12Fusion_of_fi22Slice I hG hFi
          fourAPerfect := fourAPerfect_of I hG
          fiveA := fiveAInvolutions_of I hG }

theorem twoAGraph_triangulable_Gmat_of_parts
    (I : GMSInterfaces (phiB Existence.uBar) Gmat)
    (hLO : BabyLineOddOrder) (hFi : BabyFi22Slice) (hOT : OddTypeOrdersCF tStarG xmatG)
    (hTG : ThreeCGenerated tStarG xmatG) {a : Gmat} (ha : IsConj tStarG a) :
    Triangulable (twoAGraph a) :=
  twoAGraph_triangulable_Gmat_of_isConj I (ASegFacts.of_parts I gmsF1Type_Gmat hLO hFi hOT) hFi
    hTG ha

end CFSG.Monster.Tri
