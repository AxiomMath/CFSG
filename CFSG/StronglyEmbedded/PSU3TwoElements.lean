module

public import Mathlib.GroupTheory.Sylow
import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryModelPointStructure
import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphismCoord
import CFSG.GroupTheory.WielandtProductBasic
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.Models

public section

open Matrix Polynomial

namespace CFSG.BenderSuzuki

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI CFSG.ShultStronglyClosedTI.TwoCoreGrowth
open CFSG.ShultStronglyClosedTI.UnitaryModel
open CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism
open CFSG.GroupTheory.WielandtProduct
open scoped LinearAlgebra.Projectivization

private lemma sq_eq_one_of_pow_two_pow_eq_one_fin_two {K : Type*} [Field K] [CharP K 2]
    (B : Matrix (Fin 2) (Fin 2) K) (k : ℕ) (hB : B ^ 2 ^ k = 1) : B ^ 2 = 1 := by
  set N : Matrix (Fin 2) (Fin 2) K := B - 1 with hNdef
  have hN : N ^ 2 ^ k = 0 := by
    rw [hNdef, sub_pow_char_pow_of_commute (p := 2) (n := k) (Commute.one_right B), hB,
      one_pow, sub_self]
  have hchar := Matrix.aeval_self_charpoly N
  rw [Matrix.charpoly_fin_two] at hchar
  simp only [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C,
    Algebra.algebraMap_eq_smul_one] at hchar
  rw [smul_mul_assoc, one_mul] at hchar
  have hdet : N.det = 0 := by
    have h := congrArg Matrix.det hN
    rw [Matrix.det_pow, Matrix.det_zero] at h
    exact (pow_eq_zero_iff (pow_ne_zero k (by norm_num : (2 : ℕ) ≠ 0))).mp h
  have hsq : N ^ 2 = N.trace • N := by
    have h := hchar
    rw [hdet] at h
    simp only [zero_smul, add_zero] at h
    exact sub_eq_zero.mp h
  have hpow : ∀ m : ℕ, 1 ≤ m → N ^ m = N.trace ^ (m - 1) • N := by
    intro m hm
    induction m with
    | zero => omega
    | succ m ih =>
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · subst m
        simp
      · rw [pow_succ, ih (by omega), smul_mul_assoc, ← pow_two, hsq, smul_smul, ← pow_succ,
          Nat.succ_sub_one, Nat.sub_add_cancel (by omega : 1 ≤ m)]
  have htr : N.trace = 0 := by
    by_contra htr
    have hm : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have h := hpow (2 ^ k) hm
    rw [hN] at h
    have hNzero : N = 0 := by
      rcases smul_eq_zero.mp h.symm with hc | hc
      · exact absurd hc (pow_ne_zero _ htr)
      · exact hc
    rw [hNzero, Matrix.trace_zero] at htr
    exact htr rfl
  have hNsq : N ^ 2 = 0 := by rw [hsq, htr, zero_smul]
  have hB1 : B = 1 + N := by
    rw [hNdef]
    abel
  rw [hB1, add_pow_char_of_commute (p := 2) (Commute.one_left N), one_pow, hNsq, add_zero]

private theorem middle_row_zero_of_unitary_of_middle_column_zero
    {K : Type*} [Field K] (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {A : GL (Fin 3) K} (hA : A ∈ J.unitarySubgroup)
    (h01 : (A : Matrix (Fin 3) (Fin 3) K) 0 1 = 0)
    (h21 : (A : Matrix (Fin 3) (Fin 3) K) 2 1 = 0) :
    (A : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 ∧ (A : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 := by
  let M : Matrix (Fin 3) (Fin 3) K := A
  have hdet : M.det = M 1 1 * (M 0 0 * M 2 2 - M 0 2 * M 2 0) := by
    dsimp only [M]
    simp only [Matrix.det_fin_three, h01, h21]
    ring
  have h11 : M 1 1 ≠ 0 := by
    intro h
    exact A.det_ne_zero (by rw [hdet, h, zero_mul])
  have hgram := (J.mem_unitarySubgroup_iff A).mp hA
  have hfirst : J.conj (M 1 1) * M 1 0 = 0 := by
    simpa [M, hJ, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three, h01, h21]
      using congrArg (fun B => B 1 0) hgram
  have hlast : J.conj (M 1 1) * M 1 2 = 0 := by
    simpa [M, hJ, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three, h01, h21]
      using congrArg (fun B => B 1 2) hgram
  have hconj11 : J.conj (M 1 1) ≠ 0 := (map_ne_zero J.conj).mpr h11
  exact ⟨(mul_eq_zero.mp hfirst).resolve_left hconj11,
    (mul_eq_zero.mp hlast).resolve_left hconj11⟩

private lemma submatrix_pow_succ_of_middle_row_zero {K : Type*} [Field K]
    (A : Matrix (Fin 3) (Fin 3) K)
    (h10 : A 1 0 = 0) (h12 : A 1 2 = 0) (n : ℕ) :
    (A.submatrix ![0, 2] ![0, 2]) ^ (n + 1) = (A ^ (n + 1)).submatrix ![0, 2] ![0, 2] := by
  induction n with
  | zero => rw [pow_one, pow_one]
  | succ n ih =>
    rw [pow_succ, ih]
    have hpow : A ^ (n + 1 + 1) = A ^ (n + 1) * A := by rw [pow_succ]
    rw [hpow]
    ext i j
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, Fin.sum_univ_two, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;> simp [h10, h12]

private lemma middle_entry_pow_of_middle_column_zero {K : Type*} [Field K]
    (A : Matrix (Fin 3) (Fin 3) K) (h01 : A 0 1 = 0) (h21 : A 2 1 = 0) (n : ℕ) :
    (A ^ n) 1 1 = (A 1 1) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply, Fin.sum_univ_three, ih]
    simp [h01, h21, pow_succ]

private lemma sq_eq_smul_one_of_block_diag {K : Type*} [Field K]
    (A : Matrix (Fin 3) (Fin 3) K) (ν : K)
    (h01 : A 0 1 = 0) (h21 : A 2 1 = 0)
    (h10 : A 1 0 = 0) (h12 : A 1 2 = 0)
    (hA2 : (A.submatrix ![0, 2] ![0, 2]) ^ 2 = (ν⁻¹) ^ 2 • 1)
    (hv : A 1 1 = ν⁻¹) :
    A ^ 2 = (ν⁻¹) ^ 2 • 1 := by
  have hsub := submatrix_pow_succ_of_middle_row_zero A h10 h12 1
  have hA2' : (A ^ 2).submatrix ![0, 2] ![0, 2] = (ν⁻¹) ^ 2 • 1 := by
    rw [← hsub]
    simpa using hA2
  have h00 : (A ^ 2) 0 0 = (ν⁻¹) ^ 2 := by
    have := congrFun (congrFun hA2' 0) 0
    simpa using this
  have h02 : (A ^ 2) 0 2 = 0 := by
    have := congrFun (congrFun hA2' 0) 1
    simpa using this
  have h20 : (A ^ 2) 2 0 = 0 := by
    have := congrFun (congrFun hA2' 1) 0
    simpa using this
  have h22 : (A ^ 2) 2 2 = (ν⁻¹) ^ 2 := by
    have := congrFun (congrFun hA2' 1) 1
    simpa using this
  have h11 : (A ^ 2) 1 1 = (ν⁻¹) ^ 2 := by
    rw [middle_entry_pow_of_middle_column_zero A h01 h21 2, hv]
  have h01' : (A ^ 2) 0 1 = 0 := by
    rw [pow_two, Matrix.mul_apply, Fin.sum_univ_three]
    simp [h01, h21]
  have h10' : (A ^ 2) 1 0 = 0 := by
    rw [pow_two, Matrix.mul_apply, Fin.sum_univ_three]
    simp [h10, h12]
  have h12' : (A ^ 2) 1 2 = 0 := by
    rw [pow_two, Matrix.mul_apply, Fin.sum_univ_three]
    simp [h10, h12]
  have h21' : (A ^ 2) 2 1 = 0 := by
    rw [pow_two, Matrix.mul_apply, Fin.sum_univ_three]
    simp [h01, h21]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [h00, h02, h20, h22, h11, h01', h10', h12', h21']

private lemma eq_one_of_pow_two_pow_eq_one {K : Type*} [Field K] [CharP K 2] {x : K} {k : ℕ}
    (h : x ^ 2 ^ k = 1) : x = 1 := by
  have hN : (x - 1) ^ 2 ^ k = 0 := by
    rw [sub_pow_char_pow_of_commute (p := 2) (n := k) (Commute.one_right x), h, one_pow,
      sub_self]
  have hx : x - 1 = 0 := by
    by_contra hne
    exact hne (eq_zero_of_pow_eq_zero hN)
  exact sub_eq_zero.mp hx

private lemma two_pow_two_mul_add_one_mod_three (k : ℕ) :
    2 ^ (2 * k + 1) ≡ 2 [MOD 3] := by
  have h : 2 ^ (2 * k + 1) = 2 * 4 ^ k := by
    rw [pow_succ, pow_mul]
    norm_num
    ring
  rw [h]
  have h4 : (4 : ℕ) ≡ 1 [MOD 3] := by decide
  have h4k : 4 ^ k ≡ 1 ^ k [MOD 3] := h4.pow k
  simpa using (Nat.ModEq.mul_left 2 h4k)

private theorem middleStabilizer_scalar_data
    {K : Type*} [Field K] [Finite K] (J : HermitianForm 3 K) (f : ℕ)
    (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {g : ProjectiveSpecialUnitaryMatrixGroup J}
    (hg : g ∈ unitaryMiddleStabilizer J) {k : ℕ} (hk : g ^ 2 ^ k = 1) :
    ∃ (A : GL (Fin 3) K) (c : K),
      ProjGenLinGroup.mk A = g ∧ A ∈ J.specialSubgroup ∧
      (A : Matrix (Fin 3) (Fin 3) K) 0 1 = 0 ∧
      (A : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 ∧
      (A : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 ∧
      (A : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 ∧
      (A : Matrix (Fin 3) (Fin 3) K) ^ 2 ^ k = Matrix.scalar (Fin 3) c ∧ c ^ 3 = 1 := by
  let : Fintype K := Fintype.ofFinite K
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f * 2) (by
    simpa only [Nat.card_eq_fintype_card, ← pow_mul] using hcard)
  obtain ⟨A, hA, hAg⟩ := Subgroup.mem_map.mp g.property
  let M : Matrix (Fin 3) (Fin 3) K := A
  have hg' : (g : ProjGenLinGroup (Fin 3) K) • unitaryCoordinatePoint (K := K) 1 =
      unitaryCoordinatePoint (K := K) 1 := hg
  rw [← hAg] at hg'
  have hcol := (unitary_projective_coordinate_maps_iff A 1 1).mp hg'
  have h01 : M 0 1 = 0 := hcol 0 (by decide)
  have h21 : M 2 1 = 0 := hcol 2 (by decide)
  have hrow := middle_row_zero_of_unitary_of_middle_column_zero J hJ
    (J.specialSubgroup_le_unitarySubgroup hA) h01 h21
  have h10 : M 1 0 = 0 := hrow.1
  have h12 : M 1 2 = 0 := hrow.2
  have hkP : (ProjGenLinGroup.mk A) ^ 2 ^ k = 1 := by
    rw [hAg, ← Subgroup.coe_pow, hk, Subgroup.coe_one]
  have hkGL : A ^ 2 ^ k ∈ Subgroup.center (GL (Fin 3) K) := by
    rw [← ProjGenLinGroup.mk_eq_one, map_pow, hkP]
  obtain ⟨c, hc⟩ := GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hkGL
  have hcM : M ^ 2 ^ k = Matrix.scalar (Fin 3) c := by
    simpa [M] using hc.symm
  have hdetA : Matrix.GeneralLinearGroup.det A = 1 := (J.mem_specialSubgroup_iff A).mp hA |>.2
  have hdetM : M.det = 1 := by
    have h := congrArg Units.val hdetA
    rw [GeneralLinearGroup.val_det_apply, Units.val_one] at h
    simpa [M] using h
  have hscalar : Matrix.scalar (Fin 3) c = c • (1 : Matrix (Fin 3) (Fin 3) K) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]
  have hc3 : c ^ 3 = 1 := by
    have h := congrArg Matrix.det hcM
    rw [Matrix.det_pow, hdetM, one_pow, hscalar, Matrix.det_smul, Matrix.det_one, mul_one] at h
    simpa using h.symm
  exact ⟨A, c, hAg, hA, h01, h21, h10, h12, hcM, hc3⟩

private lemma middleStabilizer_rescale {K : Type*} [Field K] {c : K} (hc3 : c ^ 3 = 1) (k : ℕ) :
    ∃ ν : K, ν ≠ 0 ∧ ν ^ 2 ^ k = c⁻¹ := by
  have hc0 : c ≠ 0 := by
    intro hc0
    rw [hc0] at hc3
    norm_num at hc3
  refine ⟨c ^ (2 * 2 ^ k), pow_ne_zero _ hc0, ?_⟩
  rw [← pow_mul]
  have h4 : 2 ^ k * 2 ^ k = 4 ^ k := by
    rw [← pow_two, ← pow_mul, show k * 2 = 2 * k by omega, pow_mul]
    norm_num
  have hmod : 2 * 2 ^ k * 2 ^ k ≡ 2 [MOD 3] := by
    have h : 2 * 2 ^ k * 2 ^ k = 2 ^ (2 * k + 1) := by
      rw [pow_succ, pow_mul]
      norm_num
      rw [← h4]
      ring
    rw [h]
    exact two_pow_two_mul_add_one_mod_three k
  have h := pow_eq_pow_of_modEq hmod hc3
  rw [h]
  exact eq_inv_of_mul_eq_one_right (by simpa [pow_succ, mul_comm] using hc3)

private lemma outer_block_sq {K : Type*} [Field K] [CharP K 2]
    (M : Matrix (Fin 3) (Fin 3) K) {c ν : K} {k : ℕ}
    (h10 : M 1 0 = 0) (h12 : M 1 2 = 0)
    (hcM : M ^ 2 ^ k = Matrix.scalar (Fin 3) c)
    (hν : ν ^ 2 ^ k = c⁻¹) (hc0 : c ≠ 0) (hν0 : ν ≠ 0) :
    (M.submatrix ![0, 2] ![0, 2]) ^ 2 = (ν⁻¹) ^ 2 • 1 := by
  have hsub := submatrix_pow_succ_of_middle_row_zero M h10 h12 (2 ^ k - 1)
  rw [Nat.sub_add_cancel (Nat.one_le_two_pow)] at hsub
  have hA2k : (M.submatrix ![0, 2] ![0, 2]) ^ 2 ^ k = c • 1 := by
    rw [hsub, hcM]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]
  have hB : (ν • M.submatrix ![0, 2] ![0, 2]) ^ 2 ^ k = 1 := by
    rw [_root_.smul_pow, hA2k, smul_smul, hν, inv_mul_cancel₀ hc0, one_smul]
  have h := sq_eq_one_of_pow_two_pow_eq_one_fin_two
    (ν • M.submatrix ![0, 2] ![0, 2]) k hB
  rw [_root_.smul_pow] at h
  calc (M.submatrix ![0, 2] ![0, 2]) ^ 2
      = (ν ^ 2)⁻¹ • (ν ^ 2 • (M.submatrix ![0, 2] ![0, 2]) ^ 2) := by
          rw [smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 hν0), one_smul]
    _ = (ν ^ 2)⁻¹ • 1 := by rw [h]
    _ = (ν⁻¹) ^ 2 • 1 := by rw [inv_pow]

private lemma middle_entry_eq_inv {K : Type*} [Field K] [CharP K 2]
    (M : Matrix (Fin 3) (Fin 3) K) {c ν : K} {k : ℕ}
    (h01 : M 0 1 = 0) (h21 : M 2 1 = 0)
    (hcM : M ^ 2 ^ k = Matrix.scalar (Fin 3) c)
    (hν : ν ^ 2 ^ k = c⁻¹) (hc0 : c ≠ 0) :
    M 1 1 = ν⁻¹ := by
  have h1 : (M ^ 2 ^ k) 1 1 = c := by
    rw [hcM]
    simp [Matrix.scalar_apply]
  rw [middle_entry_pow_of_middle_column_zero M h01 h21 (2 ^ k)] at h1
  have h2 : (ν * M 1 1) ^ 2 ^ k = 1 := by
    rw [mul_pow, hν, h1, inv_mul_cancel₀ hc0]
  have h3 : ν * M 1 1 = 1 := eq_one_of_pow_two_pow_eq_one h2
  exact eq_inv_of_mul_eq_one_right h3

private theorem matrix_sq_eq_smul_one_of_scalar_pow {K : Type*} [Field K] [CharP K 2]
    (M : Matrix (Fin 3) (Fin 3) K) {c : K} {k : ℕ}
    (h01 : M 0 1 = 0) (h21 : M 2 1 = 0) (h10 : M 1 0 = 0) (h12 : M 1 2 = 0)
    (hcM : M ^ 2 ^ k = Matrix.scalar (Fin 3) c) (hc3 : c ^ 3 = 1) :
    ∃ ν : K, M ^ 2 = (ν⁻¹) ^ 2 • 1 ∧ M 1 1 = ν⁻¹ := by
  have hc0 : c ≠ 0 := by
    intro hc0
    rw [hc0] at hc3
    norm_num at hc3
  obtain ⟨ν, hν0, hν⟩ := middleStabilizer_rescale hc3 k
  have hA2 := outer_block_sq M h10 h12 hcM hν hc0 hν0
  have hmid := middle_entry_eq_inv M h01 h21 hcM hν hc0
  exact ⟨ν, sq_eq_smul_one_of_block_diag M ν h01 h21 h10 h12 hA2 hmid, hmid⟩

private lemma middleStabilizer_sq_eq_one_of_scalar_sq
    {K : Type*} [Field K] (J : HermitianForm 3 K) (A : GL (Fin 3) K)
    {g : ProjectiveSpecialUnitaryMatrixGroup J}
    (hAg : ProjGenLinGroup.mk A = g) {ν : K}
    (hM2 : (A : Matrix (Fin 3) (Fin 3) K) ^ 2 = (ν⁻¹) ^ 2 • 1) : g ^ 2 = 1 := by
  have hM2' : (A : Matrix (Fin 3) (Fin 3) K) ^ 2 = Matrix.scalar (Fin 3) ((ν⁻¹) ^ 2) := by
    rw [hM2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]
  have hcenter : A ^ 2 ∈ Subgroup.center (GL (Fin 3) K) := by
    rw [GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
    exact ⟨(ν⁻¹) ^ 2, by simpa using hM2'.symm⟩
  apply Subtype.ext
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  rw [show (g : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk A from hAg.symm,
    ← map_pow, ProjGenLinGroup.mk_eq_one]
  exact hcenter

private theorem sq_eq_one_of_mem_unitaryMiddleStabilizer
    {K : Type*} [Field K] [Finite K] (J : HermitianForm 3 K) (f : ℕ)
    (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {g : ProjectiveSpecialUnitaryMatrixGroup J}
    (hg : g ∈ unitaryMiddleStabilizer J) (h2 : ∃ k, g ^ 2 ^ k = 1) : g ^ 2 = 1 := by
  obtain ⟨k, hk⟩ := h2
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · have hg1 : g = 1 := by simpa using hk
    simp [hg1]
  let : Fintype K := Fintype.ofFinite K
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f * 2) (by
    simpa only [Nat.card_eq_fintype_card, ← pow_mul] using hcard)
  obtain ⟨A, c, hAg, -, h01, h21, h10, h12, hcM, hc3⟩ :=
    middleStabilizer_scalar_data J f hcard hJ hg hk
  obtain ⟨ν, hM2, -⟩ := matrix_sq_eq_smul_one_of_scalar_pow
    (A : Matrix (Fin 3) (Fin 3) K) h01 h21 h10 h12 hcM hc3
  exact middleStabilizer_sq_eq_one_of_scalar_sq J A hAg hM2

private theorem map_center_unitaryRoot_le_middle
    {K : Type*} [Field K] [Finite K] (J : HermitianForm 3 K) (f : ℕ)
    (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    (Subgroup.center ((hermitianUnipotentPSU J hJ).range)).map
        ((hermitianUnipotentPSU J hJ).range).subtype ≤ unitaryMiddleStabilizer J := by
  let : Fintype K := Fintype.ofFinite K
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f * 2) (by
    simpa only [Nat.card_eq_fintype_card, ← pow_mul] using hcard)
  rintro z ⟨w, hw, rfl⟩
  let U := (hermitianUnipotentPSU J hJ).range
  let e := unitaryCoverRootEquiv J hJ
  change (w : ProjectiveSpecialUnitaryMatrixGroup J) ∈ unitaryMiddleStabilizer J
  obtain ⟨v, hv⟩ := e.surjective w
  have hw_eq : (w : ProjectiveSpecialUnitaryMatrixGroup J) =
      hermitianUnipotentPSU J hJ v := by
    rw [← hv]
    rfl
  rw [hw_eq]
  apply (unitary_root_mem_middle_iff J hJ v).mpr
  have hv_center : v ∈ Subgroup.center (hermitianUnipotentCoord J) := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h := Subgroup.mem_center_iff.mp hw ⟨e y, (e y).property⟩
    have h' : e y * e v = e v * e y := by
      rw [hv]
      exact h
    apply e.injective
    rw [map_mul, map_mul]
    exact h'
  rw [center_eq_ker_firstCoord J (2 ^ f) hcard hfixed] at hv_center
  change Multiplicative.ofAdd v.1.1 = 1 at hv_center
  rwa [ofAdd_eq_one] at hv_center


private theorem exists_fixed_point_outside
    {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (Ω : Type*) (α : Ω)
    (rho : ProjectiveSpecialUnitaryMatrixGroup J →* Equiv.Perm Ω)
    (hstabα : (MulAction.stabilizer (Equiv.Perm Ω) α).comap rho =
      unitaryCoordinateStabilizer J 0)
    (hUB : ∀ u ∈ (hermitianUnipotentPSU J hJ).range, u ∈ unitaryCoordinateStabilizer J 0)
    (hinvB : ∀ g ∈ unitaryCoordinateStabilizer J 0, orderOf g = 2 →
      g ∈ (hermitianUnipotentPSU J hJ).range)
    (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (hS : (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) =
      (hermitianUnipotentPSU J hJ).range)
    (Q : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    {t : ProjectiveSpecialUnitaryMatrixGroup J} (ht : orderOf t = 2)
    (htQ : t ∉ (Q : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))) :
    ∃ (a : ProjectiveSpecialUnitaryMatrixGroup J) (γ : Ω),
      a • Q = S ∧ γ ≠ α ∧ rho (a * t * a⁻¹) γ = γ := by
  let G := ProjectiveSpecialUnitaryMatrixGroup J
  let B := unitaryCoordinateStabilizer J 0
  have hmemB : ∀ g : G, g ∈ B ↔ rho g α = α := fun g => by
    change g ∈ unitaryCoordinateStabilizer J 0 ↔ rho g α = α
    rw [← hstabα]
    rfl
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq G Q S
  let t' : G := a * t * a⁻¹
  have ht' : orderOf t' = 2 := by
    dsimp only [t']
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, ht]
  have ht'S : t' ∉ (S : Subgroup G) := by
    intro hmem
    apply htQ
    have hmem' : t' ∈ (a • Q : Sylow 2 G) := by rwa [ha]
    have h := (mem_smul_sylow_iff (P := Q) (g := a) (x := t')).mp hmem'
    have ht_eq : a⁻¹ * t' * a = t := by
      simp only [t']
      group
    rwa [ht_eq] at h
  obtain ⟨S', hS'⟩ := IsPGroup.exists_le_sylow (p := 2) (P := Subgroup.zpowers t')
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht', pow_one]))
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq G S S'
  have hxt : x⁻¹ * t' * x ∈ (S : Subgroup G) := by
    have hmem : t' ∈ (S' : Subgroup G) := hS' (Subgroup.mem_zpowers t')
    rw [← hx] at hmem
    exact mem_smul_sylow_iff.mp hmem
  let γ : Ω := rho x α
  have hfix : rho t' γ = γ := by
    have h1 := (hmemB _).mp (hUB _ (hS ▸ hxt))
    rwa [map_mul, map_mul, map_inv, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
      Equiv.Perm.inv_eq_iff_eq] at h1
  have hγα : γ ≠ α := by
    intro h
    apply ht'S
    have ht'B : t' ∈ B := (hmemB t').mpr (by rw [h] at hfix; exact hfix)
    exact hS ▸ (hinvB t' ht'B ht')
  exact ⟨a, γ, ha, hγα, hfix⟩

private theorem exists_conj_involution_fixing_second
    {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (Ω : Type*) (α β : Ω) (hβα : β ≠ α)
    (rho : ProjectiveSpecialUnitaryMatrixGroup J →* Equiv.Perm Ω)
    (hreg : ∀ b c : Ω, b ≠ α → c ≠ α →
      ∃! u : (hermitianUnipotentPSU J hJ).range,
        rho (u : ProjectiveSpecialUnitaryMatrixGroup J) b = c)
    {t : ProjectiveSpecialUnitaryMatrixGroup J} (ht : orderOf t = 2)
    {a : ProjectiveSpecialUnitaryMatrixGroup J} {γ : Ω}
    (hγα : γ ≠ α) (hfix : rho (a * t * a⁻¹) γ = γ) :
    ∃ (u : (hermitianUnipotentPSU J hJ).range) (t'' : ProjectiveSpecialUnitaryMatrixGroup J),
      t'' = (u : ProjectiveSpecialUnitaryMatrixGroup J) * (a * t * a⁻¹) *
        (u : ProjectiveSpecialUnitaryMatrixGroup J)⁻¹ ∧
      orderOf t'' = 2 ∧ rho t'' β = β := by
  let G := ProjectiveSpecialUnitaryMatrixGroup J
  obtain ⟨u, hu, -⟩ := hreg γ β hγα hβα
  let t'' : G := (u : G) * (a * t * a⁻¹) * (u : G)⁻¹
  have hta : orderOf (a * t * a⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, ht]
  have ht'' : orderOf t'' = 2 := by
    dsimp only [t'']
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hta]
  have htu : (rho (u : G))⁻¹ β = γ := by
    change (rho (u : G)).symm β = γ
    rw [Equiv.symm_apply_eq]
    exact hu.symm
  have ht''β : rho t'' β = β := by
    dsimp only [t'']
    rw [map_mul, map_mul, map_inv, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
      htu, hfix, hu]
  exact ⟨u, t'', rfl, ht'', ht''β⟩

private theorem involution_fixing_second_mem_middle
    {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K) (f : ℕ) (hf : 2 ≤ f)
    (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (Ω : Type*) (α β : Ω)
    (rho : ProjectiveSpecialUnitaryMatrixGroup J →* Equiv.Perm Ω)
    (hstabα : (MulAction.stabilizer (Equiv.Perm Ω) α).comap rho =
      unitaryCoordinateStabilizer J 0)
    {w t'' : ProjectiveSpecialUnitaryMatrixGroup J}
    (hw_pair : unitaryCoordinatePairPreserving J w)
    (hwβ : rho w β = α)
    (ht'' : orderOf t'' = 2) (ht''β : rho t'' β = β) :
    t'' ∈ unitaryMiddleStabilizer J := by
  let G := ProjectiveSpecialUnitaryMatrixGroup J
  let B := unitaryCoordinateStabilizer J 0
  have hmemB : ∀ g : G, g ∈ B ↔ rho g α = α := fun g => by
    change g ∈ unitaryCoordinateStabilizer J 0 ↔ rho g α = α
    rw [← hstabα]
    rfl
  have hw_mid : w ∈ unitaryMiddleStabilizer J :=
    unitary_projective_pair_preserves_middle J hJ w hw_pair
  have hw_inv_α : (rho w)⁻¹ α = β := by
    change (rho w).symm α = β
    rw [Equiv.symm_apply_eq]
    exact hwβ.symm
  have hsα : rho (w * t'' * w⁻¹) α = α := by
    simp only [map_mul, map_inv, Equiv.Perm.mul_apply, hw_inv_α, ht''β]
    exact hwβ
  have hs2 : orderOf (w * t'' * w⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, ht'']
  have hsB : w * t'' * w⁻¹ ∈ B := (hmemB _).mpr hsα
  have hs_mid : w * t'' * w⁻¹ ∈ unitaryMiddleStabilizer J :=
    unitary_entire_point_involutions_fix_middle J f hf hcard hfixed hJ hsB hs2
  have h := (unitaryMiddleStabilizer J).mul_mem
    ((unitaryMiddleStabilizer J).mul_mem ((unitaryMiddleStabilizer J).inv_mem hw_mid) hs_mid)
    hw_mid
  convert h using 1
  group

private theorem conj_center_map
    {K : Type} [Field K] (J : HermitianForm 3 K)
    (Q S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    {a u : ProjectiveSpecialUnitaryMatrixGroup J}
    (ha : a • Q = S) (huS : u ∈ (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))) :
    ∀ z ∈ (Subgroup.center (Q : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))).map
        (Q : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).subtype,
      (u * a) * z * (u * a)⁻¹ ∈
        (Subgroup.center (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))).map
          (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).subtype := by
  let G := ProjectiveSpecialUnitaryMatrixGroup J
  intro z hz
  obtain ⟨zq, hzq, rfl⟩ := hz
  have hzaS : a * (zq : G) * a⁻¹ ∈ (S : Subgroup G) := by
    have hmem : a * (zq : G) * a⁻¹ ∈ (a • Q : Sylow 2 G) := by
      rw [mem_smul_sylow_iff]
      rw [show a⁻¹ * (a * (zq : G) * a⁻¹) * a = (zq : G) by group]
      exact zq.property
    rwa [ha] at hmem
  let zS : ↥(S : Subgroup G) := ⟨a * (zq : G) * a⁻¹, hzaS⟩
  have hzS_center : zS ∈ Subgroup.center (S : Subgroup G) := by
    rw [Subgroup.mem_center_iff]
    intro s
    apply Subtype.ext
    have hsQ : a⁻¹ * (s : G) * a ∈ (Q : Subgroup G) := by
      have hsmem : (s : G) ∈ (a • Q : Sylow 2 G) := by
        rw [ha]
        exact s.property
      exact mem_smul_sylow_iff.mp hsmem
    let sq : ↥(Q : Subgroup G) := ⟨a⁻¹ * (s : G) * a, hsQ⟩
    have hcomm := Subgroup.mem_center_iff.mp hzq sq
    have hcommG : (a⁻¹ * (s : G) * a) * (zq : G) =
        (zq : G) * (a⁻¹ * (s : G) * a) := by
      simpa [sq] using congrArg (fun x : ↥(Q : Subgroup G) => (x : G)) hcomm
    calc (s : G) * (a * (zq : G) * a⁻¹)
        = a * ((a⁻¹ * (s : G) * a) * (zq : G)) * a⁻¹ := by group
      _ = a * ((zq : G) * (a⁻¹ * (s : G) * a)) * a⁻¹ := by rw [hcommG]
      _ = (a * (zq : G) * a⁻¹) * (s : G) := by group
  have hzS_map : (S : Subgroup G).subtype zS ∈
      (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype :=
    Subgroup.mem_map_of_mem (f := (S : Subgroup G).subtype) hzS_center
  let uS : ↥(S : Subgroup G) := ⟨u, huS⟩
  have hcomm_u : u * (a * (zq : G) * a⁻¹) = (a * (zq : G) * a⁻¹) * u := by
    simpa [uS, zS] using congrArg (fun x : ↥(S : Subgroup G) => (x : G))
      (Subgroup.mem_center_iff.mp hzS_center uS)
  have hconj : (u * a) * (zq : G) * (u * a)⁻¹ = a * (zq : G) * a⁻¹ := by
    calc (u * a) * (zq : G) * (u * a)⁻¹
        = u * (a * (zq : G) * a⁻¹) * u⁻¹ := by group
      _ = a * (zq : G) * a⁻¹ := by
          rw [hcomm_u]
          group
  change (u * a) * (zq : G) * (u * a)⁻¹ ∈ _
  rw [hconj]
  simpa [zS] using hzS_map

private theorem conj_closure_center_insert
    {K : Type} [Field K] (J : HermitianForm 3 K)
    (Q S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    {t pg t'' : ProjectiveSpecialUnitaryMatrixGroup J}
    (hpg_t : pg * t * pg⁻¹ = t'')
    (hpg_center : ∀ z ∈ (Subgroup.center (Q : Subgroup
        (ProjectiveSpecialUnitaryMatrixGroup J))).map (Q : Subgroup
        (ProjectiveSpecialUnitaryMatrixGroup J)).subtype,
      pg * z * pg⁻¹ ∈ (Subgroup.center (S : Subgroup
        (ProjectiveSpecialUnitaryMatrixGroup J))).map (S : Subgroup
        (ProjectiveSpecialUnitaryMatrixGroup J)).subtype)
    {g : ProjectiveSpecialUnitaryMatrixGroup J}
    (hg : g ∈ Subgroup.closure (insert t ((Subgroup.center (Q : Subgroup
      (ProjectiveSpecialUnitaryMatrixGroup J))).map (Q : Subgroup
      (ProjectiveSpecialUnitaryMatrixGroup J)).subtype : Set
      (ProjectiveSpecialUnitaryMatrixGroup J)))) :
    pg * g * pg⁻¹ ∈ Subgroup.closure (insert t'' ((Subgroup.center (S : Subgroup
      (ProjectiveSpecialUnitaryMatrixGroup J))).map (S : Subgroup
      (ProjectiveSpecialUnitaryMatrixGroup J)).subtype : Set
      (ProjectiveSpecialUnitaryMatrixGroup J))) := by
  let G := ProjectiveSpecialUnitaryMatrixGroup J
  let P : (x : G) → x ∈ Subgroup.closure (insert t ((Subgroup.center (Q : Subgroup G)).map
      (Q : Subgroup G).subtype : Set G)) → Prop :=
    fun x _ => pg * x * pg⁻¹ ∈ Subgroup.closure
      (insert t'' ((Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype : Set G))
  apply Subgroup.closure_induction (p := P)
  · intro x hx
    rcases hx with rfl | hx
    · change pg * x * pg⁻¹ ∈ Subgroup.closure _
      rw [hpg_t]
      exact Subgroup.subset_closure (Or.inl rfl)
    · change pg * x * pg⁻¹ ∈ Subgroup.closure _
      exact Subgroup.subset_closure (Or.inr (hpg_center x hx))
  · change pg * 1 * pg⁻¹ ∈ Subgroup.closure _
    simp
  · intro x y hx hy hpx hpy
    change pg * (x * y) * pg⁻¹ ∈ Subgroup.closure _
    have hxy : pg * (x * y) * pg⁻¹ = (pg * x * pg⁻¹) * (pg * y * pg⁻¹) := by group
    rw [hxy]
    exact Subgroup.mul_mem _ hpx hpy
  · intro x hx hpx
    change pg * x⁻¹ * pg⁻¹ ∈ Subgroup.closure _
    have hxinv : pg * x⁻¹ * pg⁻¹ = (pg * x * pg⁻¹)⁻¹ := by group
    rw [hxinv]
    exact Subgroup.inv_mem _ hpx
  · exact hg

private theorem unitary_sq_eq_one_of_mem_closure_center_insert
    {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K) (f : ℕ) (hf : 2 ≤ f)
    (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (Q : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    {t : ProjectiveSpecialUnitaryMatrixGroup J} (ht : orderOf t = 2)
    (htQ : t ∉ (Q : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)))
    {g : ProjectiveSpecialUnitaryMatrixGroup J}
    (hg : g ∈ Subgroup.closure (insert t ((Subgroup.center (Q : Subgroup
      (ProjectiveSpecialUnitaryMatrixGroup J))).map (Q : Subgroup
      (ProjectiveSpecialUnitaryMatrixGroup J)).subtype : Set
      (ProjectiveSpecialUnitaryMatrixGroup J))))
    (h2 : ∃ k : ℕ, g ^ 2 ^ k = 1) : g ^ 2 = 1 := by
  let G := ProjectiveSpecialUnitaryMatrixGroup J
  let Ω := unitaryIsotropicPoints J
  let α := unitaryOuterIsotropicPoint J hJ 0 (by decide)
  let β := unitaryOuterIsotropicPoint J hJ 2 (by decide)
  let U := (hermitianUnipotentPSU J hJ).range
  let B := unitaryCoordinateStabilizer J 0
  obtain ⟨-, -, -, -, -, rho, hrho, hnative, -, htwo, hstabα, hstabβ, hUnormal,
    -, hUT, -, -, -, ⟨S, hS⟩, -, hreg, -, -, -, hinvB, ⟨w, hw2, hwα, hwβ⟩, -⟩ :=
    unitary_three_point_structure J f hf hcard hfixed hJ
  have hUB : ∀ u ∈ U, u ∈ B := by
    intro u hu
    change u ∈ unitaryCoordinateStabilizer J 0
    rw [← hUT]
    exact Subgroup.mem_sup_left hu
  have hβα : β ≠ α := fun h =>
    unitaryCoordinatePoint_two_ne_zero (congrArg Subtype.val h)
  obtain ⟨a, γ, ha, hγα, hfix⟩ := exists_fixed_point_outside J hJ
    Ω α rho hstabα hUB (fun g hg ho => (hinvB g hg ho).1) S hS Q ht htQ
  obtain ⟨u, t'', ht''eq, ht'', ht''β⟩ := exists_conj_involution_fixing_second J
    hJ Ω α β hβα rho hreg ht hγα hfix
  have hw_pair : unitaryCoordinatePairPreserving J w := by
    right
    constructor
    · have h := hnative w α
      rw [hwα] at h
      simpa [α, β, unitaryOuterIsotropicPoint] using h.symm
    · have h := hnative w β
      rw [hwβ] at h
      simpa [α, β, unitaryOuterIsotropicPoint] using h.symm
  have ht''_mid : t'' ∈ unitaryMiddleStabilizer J :=
    involution_fixing_second_mem_middle J f hf hcard hfixed hJ Ω α β rho hstabα
      hw_pair hwβ ht'' ht''β
  have hZ_mid : ((Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype :
      Subgroup G) ≤ unitaryMiddleStabilizer J := by
    rw [hS]
    exact map_center_unitaryRoot_le_middle J f hcard hfixed hJ
  let pg : G := (u : G) * a
  have hpg_t : pg * t * pg⁻¹ = t'' := by
    rw [ht''eq]
    dsimp only [pg]
    group
  have huS : (u : G) ∈ (S : Subgroup G) := by rw [hS]; exact u.property
  have hpg_center := conj_center_map J Q S ha huS
  have hmem_closure := conj_closure_center_insert J Q S hpg_t hpg_center hg
  have hclosure_mid : Subgroup.closure (insert t'' ((Subgroup.center (S : Subgroup G)).map
      (S : Subgroup G).subtype : Set G)) ≤ unitaryMiddleStabilizer J := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | hx
    · exact ht''_mid
    · exact hZ_mid hx
  have hg''_mid : pg * g * pg⁻¹ ∈ unitaryMiddleStabilizer J := hclosure_mid hmem_closure
  have h2'' : ∃ k : ℕ, (pg * g * pg⁻¹) ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := h2
    refine ⟨k, ?_⟩
    rw [← MulAut.conj_apply, ← map_pow, hk, map_one]
  have hsq : (pg * g * pg⁻¹) ^ 2 = 1 :=
    sq_eq_one_of_mem_unitaryMiddleStabilizer J f hcard hJ hg''_mid h2''
  have hconj : pg * (g ^ 2) * pg⁻¹ = 1 := by
    have h := hsq
    rw [conj_pow] at h
    exact h
  calc g ^ 2 = pg⁻¹ * (pg * (g ^ 2) * pg⁻¹) * pg := by group
    _ = 1 := by rw [hconj]; group

private theorem sq_eq_one_of_mem_closure_center_insert_map
    {X Y : Type*} [Group X] [Group Y] [Finite X]
    (e : X ≃* Y) (T : Sylow 2 X) {t : X} (ht : orderOf t = 2)
    (htT : t ∉ (T : Subgroup X)) {g : X}
    (hg : g ∈ Subgroup.closure (insert t ((Subgroup.center (T : Subgroup X)).map
      (T : Subgroup X).subtype : Set X)))
    (h2 : ∃ k : ℕ, g ^ 2 ^ k = 1)
    (hY : ∀ (Q : Sylow 2 Y) {u : Y}, orderOf u = 2 → u ∉ (Q : Subgroup Y) →
      ∀ {y : Y}, y ∈ Subgroup.closure (insert u ((Subgroup.center (Q : Subgroup Y)).map
        (Q : Subgroup Y).subtype : Set Y)) →
      (∃ k : ℕ, y ^ 2 ^ k = 1) → y ^ 2 = 1) :
    g ^ 2 = 1 := by
  let Q : Sylow 2 Y := T.mapSurjective (f := e.toMonoidHom) e.surjective
  have hQ : (Q : Subgroup Y) = (T : Subgroup X).map e.toMonoidHom := by
    simp [Q]
  have htu : orderOf (e t) = 2 := by
    rw [MulEquiv.orderOf_eq, ht]
  have huQ : e t ∉ (Q : Subgroup Y) := by
    intro hmem
    apply htT
    rw [hQ] at hmem
    obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.mp hmem
    have hxt : x = t := e.injective hxe
    rwa [hxt] at hx
  have hcenter : ∀ z : ↥(T : Subgroup X), z ∈ Subgroup.center (T : Subgroup X) →
      ∀ hzQ : e (z : X) ∈ (Q : Subgroup Y),
        (⟨e (z : X), hzQ⟩ : ↥(Q : Subgroup Y)) ∈ Subgroup.center (Q : Subgroup Y) := by
    intro z hz hzQ
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    change (y : Y) * e (z : X) = e (z : X) * (y : Y)
    have hy : (y : Y) ∈ (Q : Subgroup Y) := y.property
    change (y : Y) ∈ (T : Subgroup X).map e.toMonoidHom at hy
    obtain ⟨w, hw, hwe⟩ := Subgroup.mem_map.mp hy
    rw [← hwe]
    have hcomm := congrArg (fun x : ↥(T : Subgroup X) => e (x : X))
      (Subgroup.mem_center_iff.mp hz ⟨w, hw⟩)
    simpa [map_mul] using hcomm
  have hg' : e g ∈ Subgroup.closure (insert (e t) ((Subgroup.center (Q : Subgroup Y)).map
      (Q : Subgroup Y).subtype : Set Y)) := by
    let P : (x : X) → x ∈ Subgroup.closure (insert t ((Subgroup.center (T : Subgroup X)).map
        (T : Subgroup X).subtype : Set X)) → Prop :=
      fun x _ => e x ∈ Subgroup.closure (insert (e t) ((Subgroup.center (Q : Subgroup Y)).map
        (Q : Subgroup Y).subtype : Set Y))
    apply Subgroup.closure_induction (p := P)
    · intro x hx
      rcases hx with rfl | hx
      · change e x ∈ Subgroup.closure _
        exact Subgroup.subset_closure (Or.inl rfl)
      · rcases hx with ⟨z, hz, rfl⟩
        change e (z : X) ∈ Subgroup.closure _
        have hzQ : e (z : X) ∈ (Q : Subgroup Y) := by
          rw [hQ]
          exact Subgroup.mem_map_of_mem _ z.property
        exact Subgroup.subset_closure (Or.inr
          (Subgroup.mem_map_of_mem (f := (Q : Subgroup Y).subtype)
            (hcenter z hz hzQ)))
    · change e 1 ∈ Subgroup.closure _
      simp
    · intro x y hx hy hpx hpy
      change e (x * y) ∈ Subgroup.closure _
      rw [map_mul]
      exact Subgroup.mul_mem _ hpx hpy
    · intro x hx hpx
      change e x⁻¹ ∈ Subgroup.closure _
      rw [map_inv]
      exact Subgroup.inv_mem _ hpx
    · exact hg
  have h2' : ∃ k : ℕ, (e g) ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := h2
    refine ⟨k, ?_⟩
    rw [← map_pow, hk, map_one]
  have hsq : (e g) ^ 2 = 1 := hY Q htu huQ hg' h2'
  apply e.injective
  rw [map_pow, hsq, map_one]



private theorem psu3Model_sq_eq_one_of_mem_closure_center_insert
    {n : ℕ} (hn : 2 ≤ n) (T : Sylow 2 (PSU3Model n))
    {t : PSU3Model n} (ht : orderOf t = 2) (htT : t ∉ (T : Subgroup (PSU3Model n)))
    {g : PSU3Model n}
    (hg : g ∈ Subgroup.closure (insert t ((Subgroup.center (T : Subgroup (PSU3Model n))).map
      (T : Subgroup (PSU3Model n)).subtype : Set (PSU3Model n))))
    (h2 : ∃ k : ℕ, g ^ 2 ^ k = 1) : g ^ 2 = 1 := by
  have : Finite (PSU3Model n) := by
    have : Finite (ProjGenLinGroup (Fin 3) (GaloisField 2 (2 * n))) :=
      Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
    exact Subtype.finite
  let K := FiniteField.Extension (GaloisField 2 n) 2 2
  let J : HermitianForm 3 K := binaryQuadraticHermitian n (by omega)
  have hEcard : Nat.card K = (2 ^ n) ^ 2 := by
    rw [FiniteField.natCard_extension, GaloisField.card 2 n (by omega)]
  have hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ n :=
    quadraticBinaryFrobenius_fixed_card n (by omega)
  have hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl
  obtain ⟨e⟩ := projectiveSpecialUnitary_equiv_PSU3Model J n hn hJ hEcard hfixed
  exact sq_eq_one_of_mem_closure_center_insert_map e.symm T ht htT hg h2
    (unitary_sq_eq_one_of_mem_closure_center_insert J n hn hEcard hfixed hJ)

theorem sq_eq_one_of_mem_closure_center_insert {X : Type*} [Group X] [Finite X] {n : ℕ}
    (hn : 2 ≤ n) (e : X ≃* PSU3Model n) (T : Sylow 2 X) {t : X} (ht : orderOf t = 2)
    (htT : t ∉ (T : Subgroup X)) {g : X}
    (hg : g ∈ Subgroup.closure (insert t ((Subgroup.center (T : Subgroup X)).map
      (T : Subgroup X).subtype : Set X)))
    (h2 : ∃ k : ℕ, g ^ 2 ^ k = 1) : g ^ 2 = 1 :=
  sq_eq_one_of_mem_closure_center_insert_map e T ht htT hg h2
    (psu3Model_sq_eq_one_of_mem_closure_center_insert hn)

end CFSG.BenderSuzuki
