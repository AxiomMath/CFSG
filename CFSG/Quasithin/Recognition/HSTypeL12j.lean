module

public import CFSG.Quasithin.Recognition.HSTypeK

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type*} [Group G]

namespace HSSetting

variable {z : G} {V : Subgroup G}

theorem mem_smul_sylow' {X : Type*} [Group X] {p : ℕ} {S : Sylow p X} {g x : X} :
    x ∈ g • S ↔ g⁻¹ * x * g ∈ S := by
  show x ∈ ((g • S : Sylow p X) : Subgroup X) ↔ g⁻¹ * x * g ∈ (S : Subgroup X)
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
    MulAut.smul_def, MulAut.conj_apply, inv_inv]

theorem conj_mem_K [Finite G] (h : HSSetting z V) {g k : G} (hg : g ∈ hsH z) (hk : k ∈ hsK z) :
    g * k * g⁻¹ ∈ hsK z := by
  refine ⟨(hsH z).mul_mem ((hsH z).mul_mem hg hk.1) ((hsH z).inv_mem hg),
    Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
  have hu' : g⁻¹ * u * g ∈ hsZQ z := by
    have := (Subgroup.mem_normalizer_iff.mp (h.H_le_normalizer_ZQ ((hsH z).inv_mem hg)) u).mp hu
    rwa [inv_inv] at this
  have hc := Subgroup.mem_centralizer_iff.mp hk.2 _ hu'
  calc u * (g * k * g⁻¹) = g * ((g⁻¹ * u * g) * k) * g⁻¹ := by group
    _ = g * (k * (g⁻¹ * u * g)) * g⁻¹ := by rw [hc]
    _ = g * k * g⁻¹ * u := by group

end HSSetting

end CFSG.Quasithin.HSType
