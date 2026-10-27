module

public import CFSG.RankThree.PartTwo.Sec21.Item21Res9ProofLift
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RemU43

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item21Res9Proof

open Subgroup CFSG.RankThree.PartTwo.Sec4.Item434RemU43 CFSG.LieType.Multipliers.U43
open CFSG.Assembly.LowTwoRank Matrix

namespace U43

@[expose] def uCode : List ℕ := [3, 0, 1, 4, 0, 3, 7, 2, 1, 4, 3, 0, 7, 2, 0, 3]

@[expose] def tCode : List ℕ := [3, 0, 6, 5, 0, 3, 8, 6, 3, 5, 3, 0, 8, 3, 0, 3]

@[expose] def hCode : List ℕ := [3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 6, 0, 0, 0, 0, 6]

@[expose] def cCode : List ℕ := [4, 4, 0, 0, 7, 5, 0, 0, 0, 0, 3, 0, 0, 0, 0, 3]

theorem det_u : (dec4 uCode).det = 1 := by decide +kernel

theorem unitary_u : ((dec4 uCode).map (· ^ 3))ᵀ * dec4 uCode = 1 := by decide +kernel

theorem det_t : (dec4 tCode).det = 1 := by decide +kernel

theorem unitary_t : ((dec4 tCode).map (· ^ 3))ᵀ * dec4 tCode = 1 := by decide +kernel

theorem det_h : (dec4 hCode).det = 1 := by decide +kernel

theorem unitary_h : ((dec4 hCode).map (· ^ 3))ᵀ * dec4 hCode = 1 := by decide +kernel

theorem adj_checks : mul4 uCode (adj4 uCode) = one4 ∧ mul4 tCode (adj4 tCode) = one4 ∧
    mul4 hCode (adj4 hCode) = one4 := by decide +kernel

theorem cube_checks : mul4 uCode (mul4 uCode uCode) = one4 ∧
    mul4 tCode (mul4 tCode tCode) = one4 := by decide +kernel

theorem c_check : mul4 (mul4 (mul4 uCode tCode) (adj4 uCode)) (adj4 tCode) = cCode := by
  decide +kernel

theorem c_checks : mul4 cCode uCode = mul4 uCode cCode ∧ mul4 cCode tCode = mul4 tCode cCode ∧
    mul4 cCode (mul4 cCode cCode) = one4 := by decide +kernel

theorem h_check : mul4 (mul4 hCode uCode) (adj4 hCode) = adj4 uCode := by decide +kernel

theorem c_entries : cCode.getD 0 0 = 4 ∧ cCode.getD 5 0 = 5 := by decide

@[expose] noncomputable def uE : StatedSU 4 3 F9 := suOfMat (dec4 uCode) det_u unitary_u

@[expose] noncomputable def tE : StatedSU 4 3 F9 := suOfMat (dec4 tCode) det_t unitary_t

@[expose] noncomputable def hE : StatedSU 4 3 F9 := suOfMat (dec4 hCode) det_h unitary_h

theorem toMat_uE : toMat uE = dec4 uCode := coe_suOfMat _ det_u unitary_u

theorem toMat_tE : toMat tE = dec4 tCode := coe_suOfMat _ det_t unitary_t

theorem toMat_hE : toMat hE = dec4 hCode := coe_suOfMat _ det_h unitary_h

theorem toMat_inv_of_code {g : StatedSU 4 3 F9} {c : List ℕ} (hg : toMat g = dec4 c)
    (hc : mul4 c (adj4 c) = one4) : toMat g⁻¹ = dec4 (adj4 c) := by
  have h1 : toMat g * dec4 (adj4 c) = 1 := by rw [hg, ← dec4_mul4, hc, dec4_one4]
  calc toMat g⁻¹ = toMat g⁻¹ * (toMat g * dec4 (adj4 c)) := by rw [h1, mul_one]
    _ = toMat (g⁻¹ * g) * dec4 (adj4 c) := by rw [map_mul, mul_assoc]
    _ = dec4 (adj4 c) := by rw [inv_mul_cancel, map_one, one_mul]

theorem toMat_uE_inv : toMat uE⁻¹ = dec4 (adj4 uCode) := toMat_inv_of_code toMat_uE adj_checks.1

theorem toMat_tE_inv : toMat tE⁻¹ = dec4 (adj4 tCode) :=
  toMat_inv_of_code toMat_tE adj_checks.2.1

theorem toMat_hE_inv : toMat hE⁻¹ = dec4 (adj4 hCode) :=
  toMat_inv_of_code toMat_hE adj_checks.2.2

theorem toMat_cE : toMat (uE * tE * uE⁻¹ * tE⁻¹) = dec4 cCode := by
  rw [map_mul, map_mul, map_mul, toMat_uE, toMat_tE, toMat_uE_inv, toMat_tE_inv, ← dec4_mul4,
    ← dec4_mul4, ← dec4_mul4, c_check]

theorem uE_cube : uE ^ 3 = 1 := by
  apply toMat_injective
  rw [map_pow, map_one, toMat_uE, pow_succ, pow_two, mul_assoc, ← dec4_mul4, ← dec4_mul4,
    cube_checks.1, dec4_one4]

theorem tE_cube : tE ^ 3 = 1 := by
  apply toMat_injective
  rw [map_pow, map_one, toMat_tE, pow_succ, pow_two, mul_assoc, ← dec4_mul4, ← dec4_mul4,
    cube_checks.2, dec4_one4]

theorem cE_cube : (uE * tE * uE⁻¹ * tE⁻¹) ^ 3 = 1 := by
  apply toMat_injective
  rw [map_pow, map_one, toMat_cE, pow_succ, pow_two, mul_assoc, ← dec4_mul4, ← dec4_mul4,
    c_checks.2.2, dec4_one4]

theorem cE_comm_tE : uE * tE * uE⁻¹ * tE⁻¹ * tE = tE * (uE * tE * uE⁻¹ * tE⁻¹) := by
  apply toMat_injective
  rw [map_mul, map_mul toMat tE, toMat_cE, toMat_tE, ← dec4_mul4, ← dec4_mul4, c_checks.2.1]

theorem cE_comm_uE : uE * tE * uE⁻¹ * tE⁻¹ * uE = uE * (uE * tE * uE⁻¹ * tE⁻¹) := by
  apply toMat_injective
  rw [map_mul, map_mul toMat uE, toMat_cE, toMat_uE, ← dec4_mul4, ← dec4_mul4, c_checks.1]

theorem hE_conj : hE * uE * hE⁻¹ = uE⁻¹ := by
  apply toMat_injective
  rw [map_mul, map_mul, toMat_hE, toMat_uE, toMat_hE_inv, toMat_uE_inv, ← dec4_mul4,
    ← dec4_mul4, h_check]

theorem piU_cE_ne_one : piU (uE * tE * uE⁻¹ * tE⁻¹) ≠ 1 := by
  intro h1
  obtain ⟨c, hcs⟩ := piU_eq_one_iff.mp h1
  have hsc : toMat (uE * tE * uE⁻¹ * tE⁻¹) = Matrix.scalar (Fin 4) (c : F9) := by
    rw [toMat_apply, ← hcs]
    rfl
  rw [toMat_cE] at hsc
  have h00 := congrFun (congrFun hsc 0) 0
  have h11 := congrFun (congrFun hsc 1) 1
  simp only [dec4, Matrix.of_apply, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h00 h11
  rw [show (4 * ((0 : Fin 4) : ℕ) + ((0 : Fin 4) : ℕ)) = 0 by rfl, c_entries.1] at h00
  rw [show (4 * ((1 : Fin 4) : ℕ) + ((1 : Fin 4) : ℕ)) = 5 by rfl, c_entries.2] at h11
  have : uncodeF 4 = uncodeF 5 := h00.trans h11.symm
  exact absurd this (by decide)

theorem data_UX : ∃ x t y : UX, x ^ 3 = 1 ∧ y * x * y⁻¹ = x⁻¹ ∧ x * t ≠ t * x ∧
    IsPGroup 3 (closure ({x, t} : Set UX)) := by
  refine ⟨piU uE, piU tE, piU hE, by rw [← map_pow, uE_cube, map_one],
    by rw [← map_inv, ← map_mul, ← map_mul, hE_conj, map_inv], fun h => piU_cE_ne_one ?_, ?_⟩
  · rw [map_mul, map_mul, map_mul, map_inv, map_inv, h]
    group
  · have hp := isPGroup_closure_heis (k := 1) uE_cube (by rw [pow_one]; exact tE_cube) cE_cube
      cE_comm_tE cE_comm_uE
    have := hp.map piU
    rwa [MonoidHom.map_closure, Set.image_pair] at this

end U43

theorem exists_noncentral_U43 {X : Type} [Group X] [Finite X]
    (e : X ⧸ center X ≃* CFSG.Assembly.RankThreeEven.projSU 4 3 1) (S : Sylow 3 X) :
    ∃ s ∈ (S : Subgroup X), s ^ 3 = 1 ∧ ∃ t ∈ (S : Subgroup X), s * t ≠ t * s := by
  obtain ⟨x, t, y, hx3, hy, hxt, hp⟩ := U43.data_UX
  set f : UX ≃* X ⧸ center X := projSUEquivUX.symm.trans e.symm with hf
  refine exists_noncentral_of_quotient (center X) le_rfl (x := f x) (t := f t) (y := f y)
    (by rw [← map_pow, hx3, map_one]) (by rw [← map_inv, ← map_mul, ← map_mul, hy, map_inv])
    (fun h => hxt (f.injective (by rw [map_mul, map_mul, h]))) ?_ S
  have := hp.map f.toMonoidHom
  rwa [MonoidHom.map_closure, Set.image_pair] at this

end CFSG.RankThree.PartTwo.Sec21.Item21Res9Proof
