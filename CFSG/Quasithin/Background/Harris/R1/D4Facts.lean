module

public import CFSG.Quasithin.Background.Harris.R1.D4ModelFacts
public import CFSG.Quasithin.Background.Harris.R1.D4NFacts
public import CFSG.Quasithin.Background.Harris.R1.D4V1Iso

public section

namespace CFSG.Quasithin.Background.Harris.R1.D4Vert

open CFSG.Quasithin.D4Hex CFSG.LargeExtraspecial.S63


theorem zeD_mem_normalizer_U : zeD ∈ Subgroup.normalizer (d4U : Set D) := by
  rw [Subgroup.mem_normalizer_iff]
  intro u
  refine ⟨zeD_conj_mem_U, fun h => ?_⟩
  have h6 := cj_mem_U 6 h
  have : cj 6 (zeD * u * zeD⁻¹) = u := by
    have h7 : zeD ^ 6 * (zeD * u * zeD⁻¹) * (zeD ^ 6)⁻¹ = zeD ^ 7 * u * (zeD ^ 7)⁻¹ := by group
    rw [cj, h7, zeD_pow_seven]
    group
  rwa [this] at h6

theorem normalizer_d4U_eq : Subgroup.normalizer (d4U : Set D) = d4B := by
  refine le_antisymm normalizer_d4U_le_d4B ?_
  rw [← closure_B_gens, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact Subgroup.le_normalizer y1D_mem_U
  · exact Subgroup.le_normalizer y2D_mem_U
  · exact zeD_mem_normalizer_U
  · exact Subgroup.le_normalizer r0D_mem_U

theorem d4V_le_d4H : d4V ≤ d4H := fun v hv =>
  Subgroup.mem_centralizer_singleton_iff.mpr
    (d4V_comm v hv d4z (mem_d4V_iff.mpr (Or.inr (Or.inl rfl))))

theorem d4HFacts : D4HFacts where
  z_eq := hWords_zero_eq
  x_eq := x0D_eq_vB
  a_mem := aD_mem_H
  b_mem := bD_mem_H
  card_H := card_d4H
  card_U := card_d4U'
  card_B := card_d4B
  U_le_B := d4U_le_d4B
  normalizer_U := normalizer_d4U_eq

theorem d4NFacts : D4NFacts where
  y1_mem := y1D_mem_B
  y2_mem := y2D_mem_B
  ze_mem := zeD_mem_B
  r0_mem := r0D_mem_B
  s0_mem := s0D_mem_N
  closure_B := closure_B_gens
  card_B := card_d4B
  normalizer_U := normalizer_d4U_eq
  U_le_H := d4U_le_d4B.trans inf_le_left
  V_le_H := d4V_le_d4H
  cent := centralizer_d4V_inf_d4U
  center := center_Q2_le
  kc_cent := Kc_inf_centralizer_Q2
  range_n := range_nModel
  inj_n := nModel_injective

end CFSG.Quasithin.Background.Harris.R1.D4Vert
