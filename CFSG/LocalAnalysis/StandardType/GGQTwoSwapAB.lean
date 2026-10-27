module

public import CFSG.LocalAnalysis.StandardType.GGQTwoS5Defs

public section

namespace CFSG.StandardType

open Module

@[expose] def GGQ2Lin.swapAB {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p)
    (hb : ∃! c, c ≠ D.b ∧ D.cartan D.b c ≠ 0) : GGQ2Lin p :=
  { D with a := D.b, b := D.a, a_ne_b := D.a_ne_b.symm, a_leaf := hb }

end CFSG.StandardType

end
