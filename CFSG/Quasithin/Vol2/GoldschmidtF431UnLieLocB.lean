module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLieLocA

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.LL

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.EvenBN.U4 CFSG.Quasithin.H13.F431.Un.OL

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) [CharP K 2]

theorem bar_comp (ψ : K ≃+* K) (c : K) : h.bar (ψ c) = ψ (h.bar c) := by
  rw [UnitaryFieldData.bar_apply, UnitaryFieldData.bar_apply, map_pow]

theorem fa_mem_Vx (ψ : K ≃+* K) {v : Xg h} (hv : v ∈ Vx h) : fa h ψ v ∈ Vx h := by
  obtain ⟨hA, hC⟩ := Subgroup.mem_subgroupOf.1 hv
  obtain ⟨b, c, d, hb, hd, hvx⟩ := (mem_A1 h).1 hA
  rw [hvx] at hC
  obtain ⟨-, -, hc, -⟩ := (miyamotoXGL_mem_Cu h).1 hC
  refine Subgroup.mem_subgroupOf.2 ⟨?_, ?_⟩ <;>
    rw [coe_miyamotoFieldAut_apply, hvx, glAut_miyamotoXGL]
  · exact (miyamotoXGL_mem_A1 h).2 ⟨map_zero _, by rw [bar_comp, hb], by rw [bar_comp, hd]⟩
  · exact (miyamotoXGL_mem_Cu h).2 ⟨by rw [map_zero]; exact map_zero _, by rw [bar_comp, hb],
      by rw [bar_comp, hc], by rw [bar_comp, hd]⟩

theorem fa_mem_Ux (ψ : K ≃+* K) {v : Xg h} (hv : v ∈ Ux h) : fa h ψ v ∈ Ux h := by
  obtain ⟨c, hc, hvx⟩ := Subgroup.mem_subgroupOf.1 hv
  refine Subgroup.mem_subgroupOf.2 ⟨ψ c, by rw [bar_comp, hc], ?_⟩
  rw [coe_miyamotoFieldAut_apply, hvx, glAut_miyamotoXGL]
  simp

theorem exists_of_aut_fix {φ : MulAut (Xg h)} (hφ : φ (z2X h) = z2X h) :
    ∃ (s : Xg h) (ψ : K ≃+* K), s ∈ Cx h ∧ φ = MulAut.conj s * fa h ψ := by
  obtain ⟨s, hs⟩ := exists_eq_conj_mul_fieldAut h φ
  refine ⟨s, miyamotoFieldFactor h φ, ?_, hs⟩
  have hz : s * z2X h * s⁻¹ = z2X h := by
    have e := hφ
    rw [hs, MulAut.mul_apply, fa_z2X] at e
    simpa using e
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact mul_inv_eq_iff_eq_mul.1 hz

theorem aut_Vx {φ : MulAut (Xg h)} (hφ : φ (z2X h) = z2X h) {v : Xg h} (hv : v ∈ Vx h) :
    φ v ∈ Vx h := by
  obtain ⟨s, ψ, hs, rfl⟩ := exists_of_aut_fix h hφ
  rw [MulAut.mul_apply, MulAut.conj_apply]
  exact Cx_normalizes_Vx h hs (fa_mem_Vx h ψ hv)

theorem aut_Ux {φ : MulAut (Xg h)} (hφ : φ (z2X h) = z2X h) {v : Xg h} (hv : v ∈ Ux h) :
    φ v ∈ Ux h := by
  obtain ⟨s, ψ, hs, rfl⟩ := exists_of_aut_fix h hφ
  have hu := fa_mem_Ux h ψ hv
  rw [MulAut.mul_apply, MulAut.conj_apply, mul_inv_eq_iff_eq_mul.2 (Ux_central h hs hu)]
  exact hu

end CFSG.Quasithin.H13.F431.Un.LL
