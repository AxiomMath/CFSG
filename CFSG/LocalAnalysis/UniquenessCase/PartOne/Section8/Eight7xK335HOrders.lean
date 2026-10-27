module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK335Inputs
import CFSG.GH74.Orders.Sporadic
import CFSG.Sporadic.HS
import CFSG.Sporadic.Mathieu.M11
import CFSG.Sporadic.Schreier.M23Base

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

theorem k335SporadicOrders_holds :
    K335SporadicOrders := fun _ _ =>
  ⟨fun h => CFSG.GH74.card_eq_of_isSporadic (s := .M11) CFSG.Sporadic.Mathieu.card_M11 h,
    fun h => CFSG.GH74.card_eq_of_isSporadic (s := .M12) CFSG.Sporadic.Mathieu.card_M12 h,
    fun h => CFSG.GH74.card_eq_of_isSporadic (s := .M22) CFSG.Sporadic.Mathieu.card_M22 h,
    fun h => CFSG.GH74.card_eq_of_isSporadic (s := .M23) CFSG.Sporadic.Schreier.m23_card h,
    fun h => CFSG.GH74.card_eq_of_isSporadic (s := .HS) CFSG.Sporadic.HS.card_HS h,
    fun h => CFSG.GH74.card_eq_of_isSporadic (s := .J3) CFSG.Sporadic.J3.card_J3 h⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
