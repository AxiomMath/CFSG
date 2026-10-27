module

public import CFSG.LocalAnalysis.UniquenessCase.UC22L3UniBlock
public import CFSG.LieType.SeitzGeneration.UnitaryHeisGU2
import CFSG.LinearAlgebra.ProjectivePrimePlane
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.L3Uni

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.GH74.KGroups.L3Eps
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped MatrixGroups

variable {p f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData p f F)

local notation "𝟙" => ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)

theorem rho_range (h2 : (2 : F) ≠ 0) :
    (rho h h2).range =
      (Matrix.ProjGenLinGroup.mk.comp (CFSG.LieType.SeitzGeneration.gu2 h).subtype).range := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨⟨psi h h2 y, psi_unitary h h2 y⟩, ?_⟩
    rw [MonoidHom.comp_apply]
    exact (rho_eq_mk_psi h h2 y).symm
  · rintro ⟨B, rfl⟩
    exact ⟨blockC h B, by
      rw [rho_eq_mk_psi, psi_blockC]
      rw [MonoidHom.comp_apply]
      rfl⟩

theorem card_rho_range (h2 : (2 : F) ≠ 0) :
    Nat.card (rho h h2).range = p ^ f * ((p ^ f) ^ 2 - 1) := by
  rw [rho_range]
  have : Finite F := h.finite
  let π := Matrix.ProjGenLinGroup.mk.comp (CFSG.LieType.SeitzGeneration.gu2 h).subtype
  have hker : π.ker = (CFSG.LieType.SeitzGeneration.gu2Proj h).ker := by
    ext g
    change Matrix.ProjGenLinGroup.mk (g : GL (Fin 2) F) = 1 ↔
      g ∈ (CFSG.LieType.SeitzGeneration.gu2Proj h).ker
    rw [CFSG.LieType.SeitzGeneration.mem_ker_gu2Proj]
    exact Matrix.ProjGenLinGroup.mk_eq_one
  have hc := Subgroup.card_ker_mul_card_range π
  have hc' := Subgroup.card_ker_mul_card_range (CFSG.LieType.SeitzGeneration.gu2Proj h)
  rw [hker] at hc
  have hr : Nat.card π.range = Nat.card (CFSG.LieType.SeitzGeneration.gu2Proj h).range :=
    Nat.eq_of_mul_eq_mul_left Nat.card_pos (hc.trans hc'.symm)
  exact hr.trans (CFSG.LieType.SeitzGeneration.card_range_gu2Proj h)

theorem eight_dvd (h2 : (2 : F) ≠ 0) (hq : Odd (p ^ f)) : 8 ∣ Nat.card (rho h h2).range := by
  rw [card_rho_range]
  exact (Nat.eight_dvd_sq_sub_one_of_odd hq).mul_left _

theorem psi_e (h2 : (2 : F) ≠ 0) (he : e h ∈ C h) :
    ((psi h h2 ⟨e h, he⟩ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, -1; 1, 0] := by
  let eu : primeFormUnitary h 𝟙 := ⟨eU h, (eU h).2.1⟩
  have heC : eu ∈ CenU h := by
    change SpecialLinearGroup.toGL (eSL : SL(3, F)) ∈ L3Lin.CenG F
    exact L3Lin.mem_CenG_of_entries (by rfl) (by rfl) (by rfl) (by rfl)
  have he' : piC h ⟨eu, heC⟩ = (⟨e h, he⟩ : ↥(C h)) := by
    apply Subtype.ext
    exact primeFormConjHom_eq_conj h 𝟙 (eU h)
  rw [← he', psi_piC, coe_normalizedBlock]
  have hc : L3Lin.cornerHom h2 (toCenG h ⟨eu, heC⟩) = 1 := by
    apply Units.ext
    rw [L3Lin.coe_cornerHom]
    rfl
  rw [hc]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [L3Lin.blk, eu, eU, coe_eSL, eMat]

theorem psi_r (h2 : (2 : F) ≠ 0) (hr : r h ∈ C h) :
    ((psi h h2 ⟨r h, hr⟩ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![-1, 0; 0, 1] := by
  let ru : primeFormUnitary h 𝟙 := ⟨rU h, (rU h).2.1⟩
  have hrC : ru ∈ CenU h := by
    change SpecialLinearGroup.toGL (rSL : SL(3, F)) ∈ L3Lin.CenG F
    exact L3Lin.mem_CenG_of_entries (by rfl) (by rfl) (by rfl) (by rfl)
  have he : piC h ⟨ru, hrC⟩ = (⟨r h, hr⟩ : ↥(C h)) := by
    apply Subtype.ext
    exact primeFormConjHom_eq_conj h 𝟙 (rU h)
  rw [← he, psi_piC, coe_normalizedBlock]
  have hc : L3Lin.cornerHom h2 (toCenG h ⟨ru, hrC⟩) = -1 := by
    apply Units.ext
    rw [L3Lin.coe_cornerHom]
    rfl
  rw [hc]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [L3Lin.blk, ru, rU, coe_rSL, rMat]

theorem rho_ne (h2 : (2 : F) ≠ 0) (he : e h ∈ C h) (hr : r h ∈ C h) :
    rho h h2 ⟨e h, he⟩ ≠ 1 ∧ rho h h2 ⟨r h, hr⟩ ≠ 1 ∧
      rho h h2 ⟨e h, he⟩ ≠ rho h h2 ⟨r h, hr⟩ := by
  have hz : (-1 : F) ≠ 1 := by
    intro he
    apply h2
    linear_combination -he
  constructor
  · rw [rho_eq_mk_psi]
    intro h1
    rw [Matrix.ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at h1
    obtain ⟨c, hc⟩ := h1
    have he01 := congrArg (fun A : GL (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) 0 1) hc
    rw [psi_e] at he01
    simp at he01
  constructor
  · rw [rho_eq_mk_psi]
    intro h1
    rw [Matrix.ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at h1
    obtain ⟨c, hc⟩ := h1
    have he00 := congrArg (fun A : GL (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) 0 0) hc
    have he11 := congrArg (fun A : GL (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) 1 1) hc
    rw [psi_r] at he00 he11
    simp at he00 he11
    exact hz (congrArg Units.val (he00.symm.trans he11))
  · intro hne
    have hc : rho h h2 (⟨e h, he⟩ * (⟨r h, hr⟩ : ↥(C h))⁻¹) = 1 := by
      rw [map_mul, map_inv, hne, mul_inv_cancel]
    rw [rho_eq_mk_psi, Matrix.ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at hc
    obtain ⟨c, hc⟩ := hc
    have hc' : psi h h2 ⟨e h, he⟩ = GeneralLinearGroup.scalar (Fin 2) c * psi h h2 ⟨r h, hr⟩ := by
      rw [hc, map_mul, map_inv]
      group
    have he01 := congrArg (fun A : GL (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) 0 1) hc'
    rw [Units.val_mul, psi_e, psi_r, GeneralLinearGroup.coe_scalar] at he01
    simp [Matrix.mul_apply, Fin.sum_univ_two] at he01

theorem sq_eq_one_of_comm (h2 : (2 : F) ≠ 0) (he : e h ∈ C h) (hr : r h ∈ C h)
    (g : PGL(Fin 2, F)) (hge : g * rho h h2 ⟨e h, he⟩ = rho h h2 ⟨e h, he⟩ * g)
    (hgr : g * rho h h2 ⟨r h, hr⟩ = rho h h2 ⟨r h, hr⟩ * g) : g ^ 2 = 1 := by
  let E := psi h h2 ⟨e h, he⟩
  let R := psi h h2 ⟨r h, hr⟩
  have hEM : (E : Matrix (Fin 2) (Fin 2) F) = !![0, -1; 1, 0] := psi_e h h2 he
  have hRM : (R : Matrix (Fin 2) (Fin 2) F) = !![-1, 0; 0, 1] := psi_r h h2 hr
  have hER : (E : Matrix (Fin 2) (Fin 2) F) * R =
      (-1 : F) • ((R : Matrix (Fin 2) (Fin 2) F) * E) := by
    rw [hEM, hRM]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hE2 : (E : Matrix (Fin 2) (Fin 2) F) ^ 2 = (-1 : F) • 1 := by
    rw [hEM, sq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hR2 : (R : Matrix (Fin 2) (Fin 2) F) ^ 2 = (1 : F) • 1 := by
    rw [hRM, sq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have : CharP F p := h.charP
  have hp2 : p ≠ 2 := by
    intro hp2
    have : CharP F 2 := hp2 ▸ h.charP
    exact h2 CharTwo.two_eq_zero
  have hζ : IsPrimitiveRoot (-1 : F) 2 := IsPrimitiveRoot.neg_one p hp2
  obtain ⟨X, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  obtain ⟨i, j, hij⟩ := CFSG.LinearAlgebra.ProjectivePrimePlane.exists_eq_pow_mul_pow
    hER hζ (neg_ne_zero.2 one_ne_zero) one_ne_zero hE2 hR2
    (by simpa only [rho_eq_mk_psi, E] using hge.symm)
    (by simpa only [rho_eq_mk_psi, R] using hgr.symm)
  have hE2' : Matrix.ProjGenLinGroup.mk E ^ 2 = 1 := by
    rw [← map_pow, Matrix.ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar]
    refine ⟨-1, Units.ext ?_⟩
    simpa only [Units.val_pow_eq_pow_val, GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.smul_one_eq_diagonal, Units.val_neg, Units.val_one] using hE2.symm
  have hR2' : Matrix.ProjGenLinGroup.mk R ^ 2 = 1 := by
    rw [← map_pow]
    have hR : R ^ 2 = 1 := Units.ext (by simpa using hR2)
    rw [hR, map_one]
  have hcomm : Commute (Matrix.ProjGenLinGroup.mk E) (Matrix.ProjGenLinGroup.mk R) := by
    have hE : E * R = GeneralLinearGroup.scalar (Fin 2) (-1) * (R * E) := by
      apply Units.ext
      simpa only [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul,
        Units.val_neg, Units.val_one] using hER
    have hsc : Matrix.ProjGenLinGroup.mk (GeneralLinearGroup.scalar (Fin 2) (-1 : Fˣ)) = 1 := by
      rw [Matrix.ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨-1, rfl⟩
    show Matrix.ProjGenLinGroup.mk E * Matrix.ProjGenLinGroup.mk R =
      Matrix.ProjGenLinGroup.mk R * Matrix.ProjGenLinGroup.mk E
    rw [← map_mul, hE, map_mul, hsc, one_mul, map_mul]
  rw [hij, (hcomm.pow_pow i j).mul_pow 2, ← pow_mul, ← pow_mul,
    Nat.mul_comm i 2, Nat.mul_comm j 2, pow_mul, pow_mul, hE2', hR2', one_pow, one_pow, one_mul]

theorem isPGroup_of_comm (h2 : (2 : F) ≠ 0) (he : e h ∈ C h) (hr : r h ∈ C h)
    (g : PGL(Fin 2, F)) (hge : g * rho h h2 ⟨e h, he⟩ = rho h h2 ⟨e h, he⟩ * g)
    (hgr : g * rho h h2 ⟨r h, hr⟩ = rho h h2 ⟨r h, hr⟩ * g) : ∃ n : ℕ, g ^ 2 ^ n = 1 :=
  ⟨1, by simpa using sq_eq_one_of_comm h h2 he hr g hge hgr⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.L3Uni
