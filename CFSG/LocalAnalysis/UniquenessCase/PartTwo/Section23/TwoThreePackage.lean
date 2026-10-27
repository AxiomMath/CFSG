module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsRootModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {Ch : Choice2011 G}

@[expose] def Ctx23L.Conclusions23_2 (c : Ctx23L D Ch) : Prop :=
  ∃ hV : IsElemAbelian 2 c.V, ∃ k : ℕ, 2 ≤ k ∧
    IsNaturalClassicalModule (barSub ⊥ c.V hV c.L) k ∧
    (k = c.n ∨ (2 * k = c.n ∧ IsOmegaMinus ↥(barSub ⊥ c.V hV c.L) 4 k)) ∧
    Nat.card c.U0 = 2 ^ k ∧ c.U0 = conjClosure (c.L0 ⊓ D.M) D.Z ∧ D.U ⊓ c.V = c.U0 ∧
    IrrOn (c.L0 ⊓ D.M) c.U0 ∧
    ∃ hW : IsElemAbelian 2 (W23_1 c), aBar (c.L0 ⊔ D.T) ⊥ (W23_1 c) hW ≤ k

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
