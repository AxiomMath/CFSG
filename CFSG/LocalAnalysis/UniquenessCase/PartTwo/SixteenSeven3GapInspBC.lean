module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3OddNc

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def S16GapInspBC (D : Data G) : Prop :=
  ∀ (V L : Subgroup G) (hV : IsElemAbelian 2 V), Counterex16 D ⊥ V L hV →
    ¬ OddNcCore D ⊥ V hV →
    ⁅oddBar D.M ⊥ V hV, barSub ⊥ V hV (E3.wClos V D.k D.T)⁆ = ⊥ →
    (Case168_9 D ⊥ V hV L → ∀ A ∈ E3.gammaSet V D.k D.T,
      barSub ⊥ V hV A ≤ stabSub (wTil ⊥ V hV L)) →
    Insp1613U D V

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
