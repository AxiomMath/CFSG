module

public import CFSG.Sporadic.Recognition.LyonsLocalBasic
public import CFSG.Sporadic.Recognition.McLASTransport

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Equiv Equiv.Perm Subgroup CFSG.Sporadic.Recognition.McLAS

@[expose] def qA : Perm (Fin 11) := swap 1 2 * swap 9 10

@[expose] def qB : Perm (Fin 11) := swap 4 5 * swap 9 10

theorem sign_qA : sign qA = 1 := by decide
theorem sign_qB : sign qB = 1 := by decide

theorem qA_conj_x1p : qA * x1p * qA⁻¹ = x1p⁻¹ := by decide
theorem qA_conj_x2p : qA * x2p * qA⁻¹ = x2p := by decide
theorem qA_conj_x3p : qA * x3p * qA⁻¹ = x3p := by decide
theorem qB_conj_x1p : qB * x1p * qB⁻¹ = x1p := by decide
theorem qB_conj_x2p : qB * x2p * qB⁻¹ = x2p⁻¹ := by decide
theorem qB_conj_x3p : qB * x3p * qB⁻¹ = x3p := by decide

theorem cycleType_qA : qA.cycleType = {2, 2} :=
  cycleType_swap_mul_swap_of_nodup (by decide)

theorem cycleType_qB : qB.cycleType = {2, 2} :=
  cycleType_swap_mul_swap_of_nodup (by decide)

theorem cycleType_qA_mul_qB : (qA * qB).cycleType = {2, 2} := by
  have h : qA * qB = swap 1 2 * swap 4 5 := by decide
  rw [h]
  exact cycleType_swap_mul_swap_of_nodup (by decide)

section Lifts

variable {G : Type} [Group G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}

namespace LyData

theorem exists_quaternion_lifts (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    ∃ a b : ↥(centralizer ({t} : Set G)),
      a ^ 2 = ⟨t, self_mem_centralizer_singleton t⟩ ∧
      b ^ 2 = ⟨t, self_mem_centralizer_singleton t⟩ ∧ b * a * b⁻¹ = a⁻¹ ∧
      a * x₁ * a⁻¹ = x₁⁻¹ ∧ a * x₂ * a⁻¹ = x₂ ∧ a * x₃ * a⁻¹ = x₃ ∧
      b * x₁ * b⁻¹ = x₁ ∧ b * x₂ * b⁻¹ = x₂⁻¹ ∧ b * x₃ * b⁻¹ = x₃ := by
  obtain ⟨a, ha⟩ := D.cover.exists_lift sign_qA
  obtain ⟨b, hb⟩ := D.cover.exists_lift sign_qB
  have ha2 : a ^ 2 = ⟨t, self_mem_centralizer_singleton t⟩ :=
    D.cover.sq_eq_z_of_type22 (by rw [ha]; exact cycleType_qA)
  have hb2 : b ^ 2 = ⟨t, self_mem_centralizer_singleton t⟩ :=
    D.cover.sq_eq_z_of_type22 (by rw [hb]; exact cycleType_qB)
  have hab2 : (a * b) ^ 2 = ⟨t, self_mem_centralizer_singleton t⟩ :=
    D.cover.sq_eq_z_of_type22 (by rw [map_mul, ha, hb]; exact cycleType_qA_mul_qB)
  have hanti := D.cover.anticomm_of_sq ha2 hb2 hab2
  have hz2 : (⟨t, self_mem_centralizer_singleton t⟩ : ↥(centralizer ({t} : Set G))) *
      ⟨t, self_mem_centralizer_singleton t⟩ = 1 := D.cover.z_mul_z
  have hbab : b * a * b⁻¹ = a⁻¹ := by
    have h1 : b * a = ⟨t, self_mem_centralizer_singleton t⟩ * (a * b) := by
      rw [hanti, ← mul_assoc, hz2, one_mul]
    rw [h1, D.cover.inv_eq_mul_z_of_sq ha2]
    group
  refine ⟨a, b, ha2, hb2, hbab, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine D.conj_eq_of_rho S.pow₁ (by rw [inv_pow, S.pow₁, inv_one]) ?_
    rw [ha, S.rho₁, map_inv, S.rho₁]; exact qA_conj_x1p
  · refine D.conj_eq_of_rho S.pow₂ S.pow₂ ?_
    rw [ha, S.rho₂]; exact qA_conj_x2p
  · refine D.conj_eq_of_rho S.pow₃ S.pow₃ ?_
    rw [ha, S.rho₃]; exact qA_conj_x3p
  · refine D.conj_eq_of_rho S.pow₁ S.pow₁ ?_
    rw [hb, S.rho₁]; exact qB_conj_x1p
  · refine D.conj_eq_of_rho S.pow₂ (by rw [inv_pow, S.pow₂, inv_one]) ?_
    rw [hb, S.rho₂, map_inv, S.rho₂]; exact qB_conj_x2p
  · refine D.conj_eq_of_rho S.pow₃ S.pow₃ ?_
    rw [hb, S.rho₃]; exact qB_conj_x3p

end LyData

end Lifts

end CFSG.Sporadic.Recognition.LyonsSims
