module

public import CFSG.Quasithin.Recognition.St84.G24WitDelta

public section

noncomputable section

namespace CFSG.Quasithin.F112R.St84.G24M


noncomputable def witnesses (hM : Facts) : Witnesses where
  W1 i := Classical.choose (exists_aut_M1 hM i)
  W2 j := Classical.choose (exists_aut_M2 hM j)
  W1_mem i x := mem_M2_iff_of_gB0 hM (Classical.choose (exists_aut_M1 hM i)) (by
    intro k y hy
    rw [Classical.choose_spec (exists_aut_M1 hM i) k y hy]
    exact Subgroup.list_prod_mem B0 (by
      intro z hz
      obtain ⟨l, _, rfl⟩ := List.mem_map.mp hz
      exact hM.gB0_mem_B0 l)) x
  W2_mem j x := mem_M1_iff_of_gB0 hM (Classical.choose (exists_aut_M2 hM j)) (by
    intro k y hy
    rw [Classical.choose_spec (exists_aut_M2 hM j) k y hy]
    exact Subgroup.list_prod_mem B0 (by
      intro z hz
      obtain ⟨l, _, rfl⟩ := List.mem_map.mp hz
      exact hM.gB0_mem_B0 l)) x
  W1_gB0 i k x hx := Classical.choose_spec (exists_aut_M1 hM i) k x hx
  W2_gB0 j k x hx := Classical.choose_spec (exists_aut_M2 hM j) k x hx

end CFSG.Quasithin.F112R.St84.G24M
