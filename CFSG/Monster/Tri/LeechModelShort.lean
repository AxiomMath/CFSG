module

public import CFSG.Monster.B.Cbar.Fusion
public import CFSG.Monster.B.Cbar.GenData
public import CFSG.Assembly.LowTwoRankDefs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Tri.Leech

open CFSG.Monster CFSG.Monster.Spin CFSG.Monster.Griess CFSG.Monster.Visible
  CFSG.Monster.Generated CFSG.Monster.B CFSG.Monster.B.Short

theorem trace_eq_of_mem_shortClass
    {t : SpaceB ≃ₗ[ℚ] SpaceB} (ht : t ∈ shortClass) :
    LinearMap.trace ℚ SpaceB (t : SpaceB →ₗ[ℚ] SpaceB) = 4372 := by
  obtain ⟨g, -, rfl⟩ := ht
  rw [CFSG.Monster.B.trace_conj]
  exact trace_rho_short isShortCoord_rStar

theorem mul_self_eq_one_of_mem_shortClass {t : SpaceB ≃ₗ[ℚ] SpaceB} (ht : t ∈ shortClass) :
    t * t = 1 := by
  obtain ⟨g, -, rfl⟩ := ht
  calc g * tStar * g⁻¹ * (g * tStar * g⁻¹) = g * (tStar * tStar) * g⁻¹ := by group
    _ = 1 := by rw [tStar_mul_self]; group

theorem ne_one_of_mem_shortClass {t : SpaceB ≃ₗ[ℚ] SpaceB} (ht : t ∈ shortClass) : t ≠ 1 := by
  obtain ⟨g, -, rfl⟩ := ht
  intro h
  apply tStar_ne_one
  calc tStar = g⁻¹ * (g * tStar * g⁻¹) * g := by group
    _ = 1 := by rw [h]; group

theorem isShortCoord_of_rhoEquiv_mem_shortClass
    {q : Q} (h : rhoEquiv q ∈ shortClass) :
    IsShortCoord (coordOf q) := by
  have hinv : rhoEquiv q ∈ involQmat :=
    ⟨rhoEquiv_mem_rhoQ q, ne_one_of_mem_shortClass h, mul_self_eq_one_of_mem_shortClass h⟩
  have h4372 := trace_eq_of_mem_shortClass h
  rw [involQmat_eq] at hinv
  rcases hinv with (hx | hs) | hf
  · exfalso
    rw [Set.mem_singleton_iff.1 hx, trace_xmat] at h4372
    norm_num at h4372
  · obtain ⟨r, hr, hrq⟩ := hs
    rw [← rhoEquiv_injective hrq]
    exact hr
  · exfalso
    rw [trace_of_mem_xF (Or.inr hf)] at h4372
    norm_num at h4372

theorem exists_short_of_mem_shortClass_of_mem_rhoQ
    {t : SpaceB ≃ₗ[ℚ] SpaceB}
    (ht : t ∈ shortClass) (hQ : t ∈ rhoQ) :
    ∃ r : Q, IsShortCoord (coordOf r) ∧ rhoEquiv r = t := by
  obtain ⟨q, hq⟩ := mem_rhoQ.1 hQ
  exact ⟨q, isShortCoord_of_rhoEquiv_mem_shortClass (by rw [hq]; exact ht), hq⟩

end CFSG.Monster.Tri.Leech
