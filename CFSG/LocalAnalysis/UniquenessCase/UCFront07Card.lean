module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront07

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F07

variable {G : Type} [Group G] [Finite G]

@[expose] def R74Card (D : Data G) : Prop :=
  ∀ (p : ℕ) (H : Subgroup G), Sec7Hyp D p H → Nat.card ↥(Q7 D ⊓ H) ≤ 2

end CFSG.LocalAnalysis.UniquenessCase.UC22.F07
