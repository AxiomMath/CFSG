module

public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Case34A7Data

public section

namespace CFSG.Quasithin.RonanG73

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Open
open CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem clause3 {L Γ A : Subgroup (GLV V)} {m : ℕ} (h : G93Hyp Γ A L L m)
    (hX : IsAlt 7 (↥L ⧸ Subgroup.center ↥L)) :
    IsAlt 7 ↥L ∧ (Module.finrank (ZMod 2) V = 4 ∨ Module.finrank (ZMod 2) V = 6) := by
  obtain ⟨f, -, -, -, hd⟩ := Case34A7.data h hX.some
  exact ⟨⟨f⟩, hd.elim Or.inl fun h6 => Or.inr h6.1⟩

end CFSG.Quasithin.RonanG73
