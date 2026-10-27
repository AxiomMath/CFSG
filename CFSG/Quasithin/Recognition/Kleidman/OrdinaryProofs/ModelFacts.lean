module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Recognition.J2RecCzModel

public section

namespace CFSG.Quasithin.Recognition.Kleidman.OrdinaryProofs

open CFSG.Quasithin.J2Cz CFSG.Quasithin.J2Cz.QM

theorem inl_z_mem_center : SemidirectProduct.inl z ∈ Subgroup.center J2Cz.Model := by
  rw [Subgroup.mem_center_iff]
  intro y
  ext <;> simp [aut_z, z_comm]

