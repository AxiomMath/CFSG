module

public import CFSG.Quasithin.H13.GoldschmidtI51Trans

public section

namespace CFSG.Quasithin.H13.I51

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G]

@[expose] def cj (g : G) (H : Subgroup G) : Subgroup G := H.map (MulAut.conj g).toMonoidHom

theorem mem_cj {g x : G} {H : Subgroup G} : x ∈ cj g H ↔ g⁻¹ * x * g ∈ H := by
  unfold cj
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

theorem cj_inf (g : G) (H K : Subgroup G) : cj g (H ⊓ K) = cj g H ⊓ cj g K := by
  ext x; simp only [mem_cj, Subgroup.mem_inf]

theorem cj_one (H : Subgroup G) : cj 1 H = H := by
  ext x; simp [mem_cj]

end CFSG.Quasithin.H13.I51
