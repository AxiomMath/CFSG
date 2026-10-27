module

public import CFSG.LocalAnalysis.UniquenessCase.UC22L3UniRho
import CFSG.LocalAnalysis.UniquenessCase.UC22L3LinPGL
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.L3Uni

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.GH74.KGroups.L3Eps
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped MatrixGroups

variable {F : Type} [Field F]

variable {p f : ℕ} (h : UnitaryFieldData p f F)

local notation "𝟙" => ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)

theorem not_unip (h2 : (2 : F) ≠ 0) (u : ↥(C h))
    (_h3 : Nat.Coprime (orderOf (u : MulAut (primeFormP h 𝟙))) 3)
    (hup : orderOf (rho h h2 u) = p)
    (hue : (u : MulAut (primeFormP h 𝟙)) * (e h * u * (e h)⁻¹) =
      e h * u * (e h)⁻¹ * u)
    (hur : (u : MulAut (primeFormP h 𝟙)) * (r h * u * (r h)⁻¹) =
      r h * u * (r h)⁻¹ * u) : False := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP F p := h.charP
  have hp2 : p ≠ 2 := by
    intro hp2
    have : CharP F 2 := hp2 ▸ h.charP
    exact h2 CharTwo.two_eq_zero
  have he : e h ∈ C h := by
    refine Subgroup.mem_inf.2 ⟨I_le_P h (e_mem_I h), ?_⟩
    rw [mem_centralizer_singleton_iff]
    exact (Commute.self_pow (e h) 2).eq
  have hr : r h ∈ C h := by
    refine Subgroup.mem_inf.2 ⟨I_le_P h (r_mem_I h), ?_⟩
    rw [mem_centralizer_singleton_iff]
    have he := congrArg (fun x : MulAut (primeFormP h 𝟙) => x ^ 2) (r_e h)
    have hcomm : r h * e h ^ 2 * (r h)⁻¹ = e h ^ 2 := by
      have he4 := e_pow_four h
      have hesq : (e h ^ 2)⁻¹ = e h ^ 2 := by
        apply inv_eq_of_mul_eq_one_right
        simpa only [← pow_add] using he4
      have he' : r h * e h ^ 2 * (r h)⁻¹ = (e h)⁻¹ ^ 2 := by
        change (MulAut.conj (r h)) (e h ^ 2) = _
        rw [map_pow]
        change (r h * e h * (r h)⁻¹) ^ 2 = _
        rw [r_e]
      rw [he', inv_pow, hesq]
    calc r h * e h ^ 2 = (r h * e h ^ 2 * (r h)⁻¹) * r h := by group
      _ = e h ^ 2 * r h := by rw [hcomm]
  let ec : ↥(C h) := ⟨e h, he⟩
  let rc : ↥(C h) := ⟨r h, hr⟩
  let B := psi h h2 u
  let E := psi h h2 ec
  let R := psi h h2 rc
  have hB : Matrix.ProjGenLinGroup.mk B ^ p = 1 := by
    have hpw : rho h h2 u ^ p = 1 := by
      simpa only [hup] using pow_orderOf_eq_one (rho h h2 u)
    simpa only [rho_eq_mk_psi] using hpw
  obtain ⟨mu, hmu⟩ : ∃ mu : Fˣ, GeneralLinearGroup.scalar (Fin 2) mu = B ^ p := by
    rw [← map_pow, Matrix.ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at hB
    exact hB
  have hBpow : (B : Matrix (Fin 2) (Fin 2) F) ^ p = (mu : F) • 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hmu, GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hEB : B * (E * B * E⁻¹) = (E * B * E⁻¹) * B := by
    have hc : u * (ec * u * ec⁻¹) = (ec * u * ec⁻¹) * u := Subtype.ext hue
    simpa only [map_mul, map_inv] using congrArg (psi h h2) hc
  have hRB : B * (R * B * R⁻¹) = (R * B * R⁻¹) * B := by
    have hc : u * (rc * u * rc⁻¹) = (rc * u * rc⁻¹) * u := Subtype.ext hur
    simpa only [map_mul, map_inv] using congrArg (psi h h2) hc
  have hE : (E : Matrix (Fin 2) (Fin 2) F) = !![0, -1; 1, 0] := psi_e h h2 he
  have hR : (R : Matrix (Fin 2) (Fin 2) F) = !![-1, 0; 0, 1] := psi_r h h2 hr
  have hEi : ((E⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0] := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hE]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hRi : ((R⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![-1, 0; 0, 1] := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hR]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hRBm : (B : Matrix (Fin 2) (Fin 2) F) *
      (!![1, 0; 0, -1] * (B : Matrix (Fin 2) (Fin 2) F) * !![1, 0; 0, -1]) =
      (!![1, 0; 0, -1] * (B : Matrix (Fin 2) (Fin 2) F) * !![1, 0; 0, -1]) *
        (B : Matrix (Fin 2) (Fin 2) F) := by
    have he := congrArg Units.val hRB
    simp only [Units.val_mul, hR, hRi] at he
    have hop : (!![-1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) F) = - !![1, 0; 0, -1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    simpa only [hop, neg_mul, mul_neg, neg_neg] using he
  obtain ⟨a, ha⟩ := L3Lin.eq_scalar_of_comm_conj hp2
    (by simpa only [Units.val_mul, hE, hEi] using congrArg Units.val hEB) hRBm hBpow
  have ha0 : a ≠ 0 := by
    intro ha0
    have he := B.isUnit.map Matrix.detMonoidHom |>.ne_zero
    have hdet : (B : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := he
    exact hdet (by rw [ha, ha0, zero_smul]; simp)
  have hB1 : Matrix.ProjGenLinGroup.mk B = 1 := by
    rw [Matrix.ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar]
    refine ⟨Units.mk0 a ha0, Units.ext ?_⟩
    simpa only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Units.val_mk0,
      Matrix.smul_one_eq_diagonal] using ha.symm
  have hp1 : p = 1 := by
    rw [rho_eq_mk_psi] at hup
    rw [hB1, orderOf_one] at hup
    exact hup.symm
  exact h.prime.ne_one hp1

end CFSG.LocalAnalysis.UniquenessCase.UC22.L3Uni
