module

public import CFSG.Monster.GMS.Facts.Interfaces
public import CFSG.Monster.GMS.Leech.Final
public import CFSG.Monster.GMS.TableIVOf
public import CFSG.Monster.GMS.DoubleCoverOf

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

theorem GMSInterfaces.of_baby
    {d₀ : B} {G : Type} [Group G] (hSLS : SLSStatement d₀)
    (hTV : TableVIn G) (hT3 : BabyTableIII) (hT4 : BabyTableIV) (hDC : DoubleCoverThreeSwapIn G)
    (hT4' : TableIVIn G) : GMSInterfaces d₀ G :=
  ⟨hSLS, hTV, leechStatement, hT3, hT4, hDC, leechPairStatement, leechOddPairStatement, hT4',
    leechInvolutionStatement⟩

theorem GMSInterfaces.of_babyFacts
    {d₀ : B} {G : Type} [Group G] [Finite G]
    (hSLS : SLSStatement d₀) (hTV : TableVIn G) (hT3 : BabyTableIII) (hT4 : BabyTableIV)
    (hBTS : BabyThreeSwap) : GMSInterfaces d₀ G :=
  .of_baby hSLS hTV hT3 hT4 (doubleCoverThreeSwapIn_of hT3 hBTS hTV) (tableIVIn_of hT3 hT4)

end CFSG.Monster.GMS
