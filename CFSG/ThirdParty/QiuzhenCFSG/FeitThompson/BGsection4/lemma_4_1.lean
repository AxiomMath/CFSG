module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.Defs

namespace CFSG
end CFSG
open CFSG

section Main

public theorem CFSG.lemma_4_1 {G : Type*} [Group G] (hcyc : IsCyclic (G ⧸ Subgroup.center G)) :
    IsMulCommutative G := by
  letI : IsCyclic (G ⧸ Subgroup.center G) := hcyc
  exact (QuotientGroup.mk' (Subgroup.center G)).isMulCommutative_of_isCyclic_of_ker_le_center
    (by simp [QuotientGroup.ker_mk'])

end Main
