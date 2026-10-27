module

public import CFSG.Sporadic.Fi23.Tr.Classify
public import CFSG.Sporadic.Fi23.Tr.Xi
public import CFSG.Fischer.Uniq.Fi23Facts

public section

namespace CFSG.Sporadic.Fi23

open CFSG.Fischer

theorem fi23Facts
    (hFF : Fi22Facts) : Fi23Facts trOrbit cOrbit xi24Root where
  classify T hT hne := classify hFF T hT hne
  cs_not_inj _ hΩ := cs_not_inj hΩ
  ncard_of_mem_tr _ hT := ncard_of_mem_trOrbit hT
  ncard_tr := ncard_trOrbit
  injOn_tv_image _ hT := injOn_tv_image hT
  tv_image_ne _ hT _ hf := tv_image_ne hT hf
  exists_not_commute _ hT _ hf := exists_not_commute hT hf
  xi24_D2 := xi24_D2
  xi24_MU := xi24_MU
  xi24_ED := xi24_ED

end CFSG.Sporadic.Fi23
