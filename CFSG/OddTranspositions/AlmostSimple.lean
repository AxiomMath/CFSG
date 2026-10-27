module

public import CFSG.Timmesfeld.Bridge.Asc72Defs
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.OddTranspositions

open CFSG.LocalCores
open CFSG.Timmesfeld.Bridge.Asc72

attribute [local instance] CFSG.LocalCores.layer_characteristic

variable {G : Type} [Group G] [Finite G] {D : Set G}

end CFSG.OddTranspositions
