module

public import CFSG.Sporadic.Fi22.LH.Classify
public import CFSG.Sporadic.Fi22.LH.Xi
public import CFSG.Fischer.Uniq.Fi22Facts

public section

namespace CFSG.Sporadic.Fi22

open CFSG.Fischer

theorem fi22Facts
    (hPF : PolarFacts) (hHF : HyperovalFacts) : Fi22Facts where
  exists_mem_lhOrbit _ hT hne := exists_mem_lhOrbit hPF hHF hT hne
  ncard_of_mem_lhOrbit _ _ hT := ncard_of_mem_lhOrbit hT
  ncard_lhOrbit := ncard_lhOrbit
  lhOrbit_disjoint := lhOrbit_disjoint
  lhOrbit_subset_of_invariant 𝒮 h𝒮 i _ hT𝒮 hT := lhOrbit_subset_of_invariant 𝒮 h𝒮 i hT𝒮 hT
  lhU_commute := lhU_commute
  lhU_tv := lhU_tv
  image_lhU_lhOrbit := image_lhU_lhOrbit
  injOn_tv_image _ hT := injOn_tv_image hT
  tv_image_ne _ hT _ hf := tv_image_ne hT hf
  exists_not_commute _ _ hT _ hf := exists_not_commute hT hf
  xi23_D2 := xi23_D2
  xi23_MU := xi23_MU
  xi23_ED := xi23_ED

end CFSG.Sporadic.Fi22
