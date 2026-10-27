module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsB
public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel
public import CFSG.CGT.PushingUpLit.Transport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def B17_24Bound (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V) : Prop :=
  ∀ L : Subgroup G, L ∈ calC D.M → (L.subgroupOf D.M).Normal →
    IsSpor (Bar2 L) .J2 →
    P17_24_1 D V₀ V L hV.isElemAbelian ∨ P17_24_2 D V₀ V L hV.isElemAbelian

theorem seventeen_twentyfour (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V)
    (h17_20 : R17_20At D V₀ V) (h17_23 : R17_23At D V₀ V)
    (hB24 : B17_24Bound D V₀ V hV) :
    R17_24At D V₀ V := by
  intro L c
  obtain ⟨-, hN, -⟩ := h17_20 L c
  exact hB24 L c.mem_calC hN (h17_23 L c)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

end
