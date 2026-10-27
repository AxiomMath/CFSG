module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Ctx

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def S16GapInspA (D : Data G) : Prop :=
  UC6S846.SigmaStd D →
  ∀ (V L : Subgroup G) (hV : IsElemAbelian 2 V), Counterex16 D ⊥ V L hV →
    ¬ Concl1613_2 D ⊥ V hV L →
    ⁅oddBar D.M ⊥ V hV, barSub ⊥ V hV (E3.wClos V D.k D.T)⁆ ≠ ⊥ →
    ¬ (∃ r : ℕ, 3 < r ∧ Case168_4With D ⊥ V hV L r) →
    Insp1613U D V

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
