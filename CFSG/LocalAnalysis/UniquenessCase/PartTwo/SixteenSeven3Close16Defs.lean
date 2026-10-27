module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

structure Close16Setting (D : Data G) (V L : Subgroup G) (hV : IsElemAbelian 2 V) : Prop where
  counterex : Counterex16 D ⊥ V L hV
  shape : Case168_2Shape D ⊥ V hV L (Shape168_2Ln ⊥ V hV L 4)

structure Close16Pack (D : Data G) (V L : Subgroup G) (hV : IsElemAbelian 2 V) (Y : Subgroup G) :
    Prop where
  le : Y ≤ D.M
  normal : (Y.subgroupOf D.M).Normal
  perfect : ⁅Y, Y⁆ = Y
  bar_eq : barSub ⊥ V hV Y = lBar ⊥ V hV L
  ker_eq : Y ⊓ F11.CTilde D.M ⊥ V = pCoreOf 2 Y

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
