module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenInvariantOddPSubgroupCertificateDefs

public section

namespace CFSG

namespace GorensteinWalter

abbrev CompactOrderNineFour := {i : Fin 7 // i.val < 4}
@[expose] def compactOrderNineSmallT : Equiv.Perm CompactOrderNineFour :=
  Equiv.swap ⟨0, by decide⟩ ⟨1, by decide⟩ *
    Equiv.swap ⟨2, by decide⟩ ⟨3, by decide⟩

end GorensteinWalter

end CFSG
