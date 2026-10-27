module

public import CFSG.RankThree.GF2n.Tim81.Sec5.Defs

public section

namespace CFSG.RankThree.GF2n.Tim81.Sec7

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M V : Subgroup G}

@[expose] def Stmt71TI (M V : Subgroup G) : Prop :=
  ∀ C ∈ sigmaSet M V, ∀ D ∈ sigmaSet M V,
    ⁅Pc M V, C⁆ = ⁅Pc M V, D⁆ ∨ ⁅Pc M V, C⁆ ⊓ ⁅Pc M V, D⁆ = V

end CFSG.RankThree.GF2n.Tim81.Sec7
