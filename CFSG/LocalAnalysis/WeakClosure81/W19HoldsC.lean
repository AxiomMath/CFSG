module

public import CFSG.LocalAnalysis.WeakClosure81.W19HoldsB
import CFSG.LocalAnalysis.WeakClosure81.W19TwelveHolds

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem w3Thm193_of_w3Thm162 (h162 : W3Thm162Gt2 G) : W3Thm193 G :=
  w3Thm193_of_gaps' h162 fun _ _ _ _ _ c =>
    c.gap1912_holds h162 fun _ _ hc =>
      c.card_inf_J193 h162 (fun _ _ _ V' => sevenSixThreeAbelian_holds V') hc

end CFSG.LocalAnalysis.WeakClosure81
