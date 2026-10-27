module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7DDefs
import CFSG.LocalAnalysis.StandardType.GGHdRo7DReduceVIrr
import CFSG.LocalAnalysis.StandardType.GGHdRo7DReduceVCard

public section

namespace CFSG.StandardType.HdRo7D

theorem d_reduceV_holds : DReduceVLeaf :=
  fun hN _ _ _ _ _ _ _ _ _ hD hspan hmove =>
    ⟨d_reduceV_absIrred hN hD hspan hmove, d_reduceV_card hN hD⟩

end CFSG.StandardType.HdRo7D
