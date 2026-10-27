module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4Setting
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4LocLie
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsMap
public import CFSG.Quasithin.Recognition.F4Thirtyone

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin

@[expose] noncomputable def d4Theta : D ≃* d4Setting.ι.G0 :=
  MulEquiv.ofBijective d4Phi ⟨d4Phi_injective, d4Phi_surjective⟩

theorem d4ToD_d4Theta (y : D) : d4ToD (d4Theta y) = y := rfl

theorem d4Theta_symm_eq (k : d4Setting.ι.G0) : d4Theta.symm k = d4ToD k := by
  rw [← d4ToD_d4Theta (d4Theta.symm k), MulEquiv.apply_symm_apply]

theorem d4_mem_Mb1_iff (k : d4Setting.ι.G0) : k ∈ d4Setting.Mb1 ↔ d4ToD k ∈ d4H := by
  rw [← mem_range_φ1_iff]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, Subtype.ext ha⟩

theorem d4_mem_Mb2_iff (k : d4Setting.ι.G0) : k ∈ d4Setting.Mb2 ↔ d4ToD k ∈ d4N := by
  rw [← mem_range_φ2_iff]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, Subtype.ext ha⟩

theorem d4_Mb1_eq : d4Setting.Mb1 = d4H.map d4Theta.toMonoidHom := by
  ext k
  rw [Subgroup.mem_map_equiv, d4_mem_Mb1_iff, d4Theta_symm_eq]

theorem d4_Mb2_eq : d4Setting.Mb2 = d4N.map d4Theta.toMonoidHom := by
  ext k
  rw [Subgroup.mem_map_equiv, d4_mem_Mb2_iff, d4Theta_symm_eq]

@[expose] noncomputable def d4ZH : ↥d4H :=
  ⟨d4z, (Subgroup.mem_inf.1 (d4U_le_d4B d4z_mem_d4U)).1⟩

@[expose] noncomputable def d4TH : ↥d4H :=
  ⟨d4t, (Subgroup.mem_inf.1 (d4U_le_d4B d4t_mem_d4U)).1⟩

theorem d4_F431LieI_G0 :
    F431LieI (d4U.map d4Theta.toMonoidHom) d4Setting.Mb1 d4Setting.Mb2 (d4Theta d4z)
      (d4Theta d4t) := by
  rw [d4_Mb1_eq, d4_Mb2_eq]
  exact F431LieI.map d4Theta d4_F431LieI

end CFSG.Quasithin.D4Hex
