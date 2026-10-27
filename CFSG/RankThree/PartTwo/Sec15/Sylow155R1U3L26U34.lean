module

public import CFSG.RankThree.PartTwo.KFacts.KS21U34
public import CFSG.Models.PGL
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSCLinearDegree

public noncomputable section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG.PGLModel (projSU)
open CFSG.GH74.KGroups CFSG.RankThree.PartTwo.KFacts.KS21.U34
open CFSG.ComponentClassification.UnbalancedGS.LinearDegree (pow_two_pow_eq_one_of_le)

private theorem nonempty_mulEquiv_Y : Nonempty (projSU 3 2 2 ≃* Y) :=
  nonempty_equiv_Y (CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU
    ⟨Nat.prime_two, by norm_num, le_rfl, by decide⟩ (MulEquiv.refl _))

private def matHom : Y →* Mat3 := (Units.coeHom Mat3).comp Y.subtype

private theorem matHom_injective : Function.Injective matHom := mat_injective

private def m3 (a b c d e f g h i : ℕ) : Mat3 :=
  !![GF16.ofNat' a, GF16.ofNat' b, GF16.ofNat' c; GF16.ofNat' d, GF16.ofNat' e, GF16.ofNat' f;
    GF16.ofNat' g, GF16.ofNat' h, GF16.ofNat' i]

private def gM : Mat3 := m3 11 11 5 10 6 11 7 14 3

private def gInvM : Mat3 := m3 2 13 4 9 6 13 7 12 13

private def xM : Mat3 := m3 6 10 9 2 7 5 2 15 1

private def xInvM : Mat3 := m3 1 4 14 8 7 12 3 3 6

private def g2M : Mat3 := m3 3 5 7 15 13 5 11 7 5

private def g3M : Mat3 := m3 12 15 7 0 8 15 2 11 10

private def g4M : Mat3 := m3 7 5 3 4 0 5 4 12 14

private def g8M : Mat3 := m3 13 15 10 8 14 15 7 3 14

private theorem gM_mul_gInvM : gM * gInvM = 1 := by decide

private theorem gInvM_mul_gM : gInvM * gM = 1 := by decide

private theorem xM_mul_xInvM : xM * xInvM = 1 := by decide

private theorem xInvM_mul_xM : xInvM * xM = 1 := by decide

private theorem det3_gM : det3 gM = 1 := by decide

private theorem isGU3_gM : IsGU3 gM := by decide

private theorem det3_xM : det3 xM = 1 := by decide

private theorem isGU3_xM : IsGU3 xM := by decide

private theorem gM_ne_one : gM ≠ 1 := by decide

private theorem gM_mul_gM : gM * gM = g2M := by decide

private theorem g2M_mul_gM : g2M * gM = g3M := by decide

private theorem g2M_mul_g2M : g2M * g2M = g4M := by decide

private theorem g4M_mul_g4M : g4M * g4M = g8M := by decide

private theorem g8M_mul_g4M_mul_gM : g8M * g4M * gM = 1 := by decide

private theorem xM_mul_gM : xM * gM = g3M * xM := by decide

private theorem gM_pow_three : gM ^ 3 = g3M := by
  rw [pow_three', gM_mul_gM, g2M_mul_gM]

private theorem gM_pow_thirteen : gM ^ 13 = 1 := by
  have h2 : gM ^ 2 = g2M := by rw [sq, gM_mul_gM]
  have h4 : gM ^ 4 = g4M := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h2, sq, g2M_mul_g2M]
  have h8 : gM ^ 8 = g8M := by rw [show (8 : ℕ) = 4 * 2 from rfl, pow_mul, h4, sq, g4M_mul_g4M]
  calc gM ^ 13 = gM ^ 8 * gM ^ 4 * gM := by rw [← pow_add, ← pow_succ]
    _ = 1 := by rw [h8, h4, g8M_mul_g4M_mul_gM]

private def gGL : GL (Fin 3) GF16 := ⟨gM, gInvM, gM_mul_gInvM, gInvM_mul_gM⟩

private def xGL : GL (Fin 3) GF16 := ⟨xM, xInvM, xM_mul_xInvM, xInvM_mul_xM⟩

private def gY : Y := ⟨gGL, (mem_Y_iff gGL).2 ⟨det3_gM, isGU3_gM⟩⟩

private def xY : Y := ⟨xGL, (mem_Y_iff xGL).2 ⟨det3_xM, isGU3_xM⟩⟩

private theorem matHom_gY : matHom gY = gM := rfl

private theorem matHom_xY : matHom xY = xM := rfl

private theorem gY_pow_thirteen : gY ^ 13 = 1 := by
  apply matHom_injective
  rw [map_pow, map_one, matHom_gY]
  exact gM_pow_thirteen

private theorem orderOf_gY : orderOf gY = 13 := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  refine orderOf_eq_prime gY_pow_thirteen fun h => gM_ne_one ?_
  have := congrArg matHom h
  rwa [matHom_gY, map_one] at this

private theorem xY_conj : xY * gY * xY⁻¹ = gY ^ 3 := by
  rw [mul_inv_eq_iff_eq_mul]
  apply matHom_injective
  rw [map_mul, map_mul, map_pow, matHom_gY, matHom_xY, gM_pow_three]
  exact xM_mul_gM

theorem exists_orderOf_thirteen_conj_cube_projSU :
    ∃ g x : projSU 3 2 2, orderOf g = 13 ∧ x * g * x⁻¹ = g ^ 3 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_Y
  refine ⟨e.symm gY, e.symm xY, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq]
    exact orderOf_gY
  · have h := congrArg e.symm xY_conj
    rwa [map_mul, map_mul, map_inv, map_pow] at h

theorem pow_four_eq_one_of_pow_eight_projSU (g : projSU 3 2 2) (hg : g ^ 8 = 1) : g ^ 4 = 1 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_Y
  have h8 : (Y.subtype (e g)) ^ (2 ^ 3) = 1 := by
    rw [← map_pow, ← map_pow, show (2 : ℕ) ^ 3 = 8 from rfl, hg, map_one, map_one]
  have h4 := pow_two_pow_eq_one_of_le (k := GF16) (d := 3) (by norm_num) h8 (j := 2) (by norm_num)
  have h4' : (e g) ^ 4 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact h4
  exact (MulEquiv.map_eq_one_iff e).mp (by rw [map_pow]; exact h4')

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
