module

public import CFSG.Quasithin.H13.GoldschmidtU43BStruct

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

theorem mem_Hz_conj {x y g : G} : y ∈ Hz (g * x * g⁻¹) ↔ g⁻¹ * y * g ∈ Hz x := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc g⁻¹ * y * g * x = g⁻¹ * (y * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * y) * g := by rw [h]
      _ = x * (g⁻¹ * y * g) := by group
  · intro h
    calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [h]
      _ = (g * x * g⁻¹) * y := by group

theorem Hz_conj (x g : G) :
    Hz (g * x * g⁻¹) = (Hz x).map (MulAut.conj g).toMonoidHom := by
  ext y
  rw [mem_Hz_conj, Subgroup.mem_map_equiv]
  rfl

theorem mem_Uz_conj {x y g : G} : y ∈ Uz (g * x * g⁻¹) ↔ g⁻¹ * y * g ∈ Uz x := by
  have h : Uz (g * x * g⁻¹) = (Uz x).map (MulAut.conj g).toMonoidHom := by
    show pCoreOf 2 (Hz (g * x * g⁻¹)) = (pCoreOf 2 (Hz x)).map (MulAut.conj g).toMonoidHom
    rw [Hz_conj]
    exact CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.conj g) (Hz x)
  rw [h, Subgroup.mem_map_equiv]
  rfl

namespace Hyp

variable {z : G} (h : Hyp z)
include h

theorem z_mem_Uz_of_mem_S [Finite G] {t : G} (ht : t ∈ S z) : z ∈ Uz t := by
  obtain ⟨w, s⟩ := h.exists_swap_data ht
  have e : t = w⁻¹ * z * w⁻¹⁻¹ := by rw [inv_inv]; exact s.w1.symm
  rw [e, mem_Uz_conj]
  simp only [inv_inv]
  rw [s.w1']
  exact ht.1

end Hyp

end CFSG.Quasithin.H13.U43
