module

public import CFSG.Timmesfeld.Bridge.RootStructBasic

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

variable {G : Type*} [Group G]

@[expose] def lineN (D : Set G) (a d : G) : Subgroup G :=
  (nCore D a ⊓ Subgroup.centralizer {d}) ⊔ (nCore D d ⊓ Subgroup.centralizer {a})

@[expose] def lineN₀ (D : Set G) (a d : G) : Subgroup G :=
  nCore D a ⊓ nCore D d

end CFSG.Timmesfeld.Bridge
