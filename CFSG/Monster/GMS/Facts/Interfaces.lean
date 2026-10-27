module

public import CFSG.Monster.GMS.Facts.DoubleCover
public import CFSG.Monster.GMS.Facts.LeechInvolutions
public import CFSG.Monster.GMS.Facts.LeechOddPairs
public import CFSG.Monster.GMS.Facts.LeechPairs
public import CFSG.Monster.GMS.Facts.TableIV

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

structure GMSInterfaces (d₀ : B) (G : Type) [Group G] : Prop where
  sls : SLSStatement d₀
  tableV : TableVIn G
  leech : LeechStatement
  tableIII : BabyTableIII
  tableIVBaby : BabyTableIV
  threeSwap : DoubleCoverThreeSwapIn G
  leechPair : LeechPairStatement
  leechOddPair : LeechOddPairStatement
  tableIV : TableIVIn G
  leechInv : LeechInvolutionStatement

theorem GMSInterfaces.of_universal {d₀ : B} (hSLS : SLSStatement d₀) (hTV : TableVStatement)
    (hL : LeechStatement) (hT3 : BabyTableIII) (hT4 : BabyTableIV)
    (hDC : DoubleCoverThreeSwapStatement) (hLP : LeechPairStatement)
    (hLO : LeechOddPairStatement) (hT4' : TableIVStatement) (hLI : LeechInvolutionStatement)
    (G : Type) [Group G] [Finite G] : GMSInterfaces d₀ G :=
  ⟨hSLS, hTV.inG, hL, hT3, hT4, hDC.inG, hLP, hLO, hT4'.inG, hLI⟩

end CFSG.Monster.GMS
