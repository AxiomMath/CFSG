module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4D3Inn
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4AutStab

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin

theorem mem_autStab_H_of_apply_z {β : MulAut D} (h : β d4z = d4z) : β ∈ autStab d4H := by
  intro x
  rw [mem_d4H_iff_mul_z, mem_d4H_iff_mul_z]
  constructor
  · intro hx
    have := congrArg β hx
    rwa [map_mul, map_mul, h] at this
  · intro hx
    apply β.injective
    rw [map_mul, map_mul, h]
    exact hx

section Outer


theorem exists_aut_stab_not_inner (hne : (MulAut.conj : D →* MulAut D).range ≠ ⊤) :
    ∃ β : MulAut D, β ∈ autStab d4H ∧ β ∉ (MulAut.conj : D →* MulAut D).range := by
  obtain ⟨α, hα⟩ : ∃ α : MulAut D, α ∉ (MulAut.conj : D →* MulAut D).range := by
    by_contra h
    push Not at h
    exact hne (eq_top_iff.2 fun α _ => h α)
  obtain ⟨j, hj⟩ := exists_aut_zElt α ⟨0, by norm_num⟩
  obtain ⟨g, hg⟩ := exists_smul_pt0_eq j
  have h1 := zElt_act g pt0
  rw [← smul_pt_def, hg, zElt_zero] at h1
  rw [zElt_zero] at hj
  have hgz : α d4z = g * d4z * g⁻¹ := hj.trans h1
  refine ⟨(MulAut.conj g)⁻¹ * α, mem_autStab_H_of_apply_z ?_, fun hmem => hα ?_⟩
  · rw [MulAut.mul_apply, hgz, ← map_inv, MulAut.conj_apply]
    group
  · simpa using (MulAut.conj : D →* MulAut D).range.mul_mem ⟨g, rfl⟩ hmem

theorem d3_K3_eq_top_of
    (hint : ∀ M : Subgroup (MulAut D), (MulAut.conj : D →* MulAut D).range ≤ M →
      M = (MulAut.conj : D →* MulAut D).range ∨ M = ⊤)
    (hne : (MulAut.conj : D →* MulAut D).range ≠ ⊤) : autStab d4H ⊔ autStab d4N = ⊤ := by
  rcases hint _ inn_le_K3 with h | h
  · exfalso
    obtain ⟨β, hβ, hβn⟩ := exists_aut_stab_not_inner hne
    exact hβn (h ▸ (le_sup_left : autStab d4H ≤ autStab d4H ⊔ autStab d4N) hβ)
  · exact h

end Outer

section Top

variable
  {D' : Type} [Group D'] (hD' : IsLieOverTwo .trialityD4 0 1 D')

include hD' in
theorem d3_K3_eq_top : autStab d4H ⊔ autStab d4N = ⊤ := by
  refine d3_K3_eq_top_of (d4_aut_intermediate hD') fun h => ?_
  have := d4_conj_index hD'
  rw [h, Subgroup.index_top] at this
  norm_num at this

end Top

end CFSG.Quasithin.D4Hex
