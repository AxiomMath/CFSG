module

public import CFSG.CGT.Timmesfeld75.Defs
public import CFSG.RankThree.GF2n.Tim78S4Extra

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def RootTypeStep (M B : Subgroup G) : Prop :=
  ∀ g b : G, b ∈ B → b ≠ 1 → g * b * g⁻¹ ∈ M → conjSubgroup g B ≤ M

end CFSG.RankThree.GF2n.Tim78
