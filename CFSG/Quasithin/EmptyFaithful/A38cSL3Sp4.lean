module

public import CFSG.Quasithin.EmptyFaithful.S153F20
public import CFSG.Quasithin.H13.VolIA38SLThree
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.A38cOrders

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.H13.VolI

theorem sl3Sp4NotA38Type_holds :
    SL3Sp4NotA38Type := by
  intro G _ _ L h hA
  rcases h with ⟨n, F, _, _, hn, hF, ⟨e⟩⟩ | ⟨F, _, _, hF, ⟨e⟩⟩
  · have hF' : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
    have := a38TypesSLThree_holds (↥L ⧸ CFSG.pCore 2 ↥L) F n hF' ⟨e⟩ hA
    omega
  · have hF' : Nat.card F = 2 ^ 2 := by rw [Nat.card_eq_fintype_card, hF]; norm_num
    have hcard : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 979200 := by
      rw [Nat.card_congr e.toEquiv, Vol2.Ch10.SecA.card_Sp4_pow hF']
      norm_num
    exact not_a38Order_979200 (hcard ▸ a38Order_card hA)

end CFSG.Quasithin
