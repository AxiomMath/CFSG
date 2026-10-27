module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KRadSetup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105

open CFSG.Open Subgroup Matrix
open CFSG.Assembly.LowTwoRank (StatedSU)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LinearGroups (stdHermForm)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f ε : ℕ}
  {b : StatedSU (2 * 2 + ε) (2 ^ f) K} {ω : K}

omit [Finite K] [CharP K 2] in
private theorem bar_omega (hS : RadSetup ε b ω) (h : UnitaryFieldData 2 f K) :
    h.bar ω = ω := by
  have hmod : 2 ^ f ≡ 1 [MOD 3] := by
    obtain ⟨m, hm⟩ := hS.even
    have h4 : 4 ^ m ≡ 1 [MOD 3] := by
      have h := (show (4 : ℕ) ≡ 1 [MOD 3] by decide).pow m
      simpa using h
    have hf : f = 2 * m := by omega
    have hpow : 2 ^ f = 4 ^ m := by
      rw [hf, pow_mul]
      norm_num
    rw [hpow]
    exact h4
  rw [h.bar_apply]
  simpa using pow_eq_pow_of_modEq hmod hS.cube

omit [Finite K] [CharP K 2] in
private theorem one_add_omega_add_sq (hS : RadSetup ε b ω) : 1 + ω + ω ^ 2 = 0 := by
  have h : (ω - 1) * (1 + ω + ω ^ 2) = 0 := by
    have h' : (ω - 1) * (1 + ω + ω ^ 2) = ω ^ 3 - 1 := by ring
    rw [h', hS.cube, sub_self]
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hS.ne_one)

omit [Finite K] [CharP K 2] in
private theorem omega_sq_ne_one (hS : RadSetup ε b ω) : ω ^ 2 ≠ 1 := by
  intro h
  have h3 : ω ^ 3 = ω := by
    rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, h, one_mul]
  rw [hS.cube] at h3
  exact hS.ne_one h3.symm

omit [Finite K] [CharP K 2] in
private theorem omega_ne_zero (hS : RadSetup ε b ω) : ω ≠ 0 := by
  intro h
  simpa [h] using hS.cube

omit [Finite K] [CharP K 2] in
private theorem omega_inv_eq (hS : RadSetup ε b ω) : ω⁻¹ = ω ^ 2 := by
  have h : ω * ω ^ 2 = 1 := by
    calc ω * ω ^ 2 = ω ^ 3 := by ring
    _ = 1 := hS.cube
  exact inv_eq_of_mul_eq_one_right h

omit [Finite K] [CharP K 2] in
private theorem omega_ne_inv (hS : RadSetup ε b ω) : ω ≠ ω⁻¹ := by
  intro h
  have h2 : ω ^ 2 = 1 := by
    have h' : ω * ω = ω * ω⁻¹ := congrArg (fun x => ω * x) h
    simpa [pow_two, mul_inv_cancel₀ (omega_ne_zero hS)] using h'
  exact omega_sq_ne_one hS h2

omit [Finite K] in
private theorem three_eq_one : (3 : K) = 1 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h3 : (3 : K) = 2 + 1 := by norm_num
  rw [h3, h2, zero_add]

omit [Finite K] [CharP K 2] in
theorem RadSetup.isotropic (hS : RadSetup ε b ω) (h : UnitaryFieldData 2 f K) :
    ∀ v ∈ eigSU b ω, ∀ w ∈ eigSU b ω, stdHermForm h (2 * 2 + ε) v w = 0 := by
  intro v hv w hw
  rw [mem_eigSU] at hv hw
  have hiso : stdHermForm h (2 * 2 + ε)
      (((b : GL (Fin (2 * 2 + ε)) K) : Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) K) *ᵥ v)
      (((b : GL (Fin (2 * 2 + ε)) K) : Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) K) *ᵥ w) =
      stdHermForm h (2 * 2 + ε) v w :=
    (CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff_isometry h).mp b.2 |>.2 v w
  rw [hv, hw] at hiso
  have hlin : stdHermForm h (2 * 2 + ε) (ω • v) (ω • w) =
      h.bar ω * ω * stdHermForm h (2 * 2 + ε) v w := by
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
  rw [bar_omega hS h] at hlin
  have hfix : stdHermForm h (2 * 2 + ε) v w =
      ω ^ 2 * stdHermForm h (2 * 2 + ε) v w := by
    calc stdHermForm h (2 * 2 + ε) v w
        = stdHermForm h (2 * 2 + ε) (ω • v) (ω • w) := hiso.symm
      _ = ω * ω * stdHermForm h (2 * 2 + ε) v w := hlin
      _ = ω ^ 2 * stdHermForm h (2 * 2 + ε) v w := by ring
  have hzero : (1 - ω ^ 2) * stdHermForm h (2 * 2 + ε) v w = 0 := by
    rw [sub_mul, one_mul, hfix.symm, sub_self]
  exact (mul_eq_zero.mp hzero).resolve_left
    (sub_ne_zero.mpr (Ne.symm (omega_sq_ne_one hS)))

omit [Finite K] [CharP K 2] in
theorem RadSetup.orth_one (hS : RadSetup ε b ω) (h : UnitaryFieldData 2 f K) :
    ∀ v ∈ eigSU b 1, ∀ w ∈ eigSU b ω,
      stdHermForm h (2 * 2 + ε) v w = 0 ∧ stdHermForm h (2 * 2 + ε) w v = 0 := by
  intro v hv w hw
  rw [mem_eigSU] at hv hw
  have hiso : stdHermForm h (2 * 2 + ε)
      (((b : GL (Fin (2 * 2 + ε)) K) : Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) K) *ᵥ v)
      (((b : GL (Fin (2 * 2 + ε)) K) : Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) K) *ᵥ w) =
      stdHermForm h (2 * 2 + ε) v w :=
    (CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff_isometry h).mp b.2 |>.2 v w
  rw [hv, hw, one_smul] at hiso
  have hlin : stdHermForm h (2 * 2 + ε) v (ω • w) =
      ω * stdHermForm h (2 * 2 + ε) v w := by
    rw [map_smul, smul_eq_mul]
  have hfix : stdHermForm h (2 * 2 + ε) v w = ω * stdHermForm h (2 * 2 + ε) v w := by
    calc stdHermForm h (2 * 2 + ε) v w
        = stdHermForm h (2 * 2 + ε) v (ω • w) := hiso.symm
      _ = ω * stdHermForm h (2 * 2 + ε) v w := hlin
  have hzero : (1 - ω) * stdHermForm h (2 * 2 + ε) v w = 0 := by
    rw [sub_mul, one_mul, hfix.symm, sub_self]
  have hvw : stdHermForm h (2 * 2 + ε) v w = 0 :=
    (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr (Ne.symm hS.ne_one))
  refine ⟨hvw, ?_⟩
  have hsym := (CFSG.LinearGroups.stdHermForm_isSymm h (2 * 2 + ε)).eq v w
  rw [hvw, map_zero] at hsym
  exact hsym.symm

private abbrev bMat {K : Type} [Field K] {f ε : ℕ}
    (b : StatedSU (2 * 2 + ε) (2 ^ f) K) :
    Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) K :=
  ((b : GL (Fin (2 * 2 + ε)) K) : Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) K)

omit [Finite K] [CharP K 2] in
private theorem decomp_b_pow_three (hS : RadSetup ε b ω) : (bMat b) ^ 3 = 1 := by
  have h := congrArg (fun z : StatedSU (2 * 2 + ε) (2 ^ f) K =>
    ((z : GL (Fin (2 * 2 + ε)) K) :
      Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) K)) hS.pow_three
  simpa [bMat] using h

omit [Finite K] [CharP K 2] in
private theorem decomp_eig_one (hS : RadSetup ε b ω) (v : Fin (2 * 2 + ε) → K) :
    (1 + bMat b + (bMat b) ^ 2) *ᵥ v ∈ eigSU b 1 := by
  let B : Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) K := bMat b
  change (1 + B + B ^ 2) *ᵥ v ∈ eigSU b 1
  have hB3 : B ^ 3 = 1 := decomp_b_pow_three hS
  rw [mem_eigSU]
  change B *ᵥ ((1 + B + B ^ 2) *ᵥ v) = 1 • ((1 + B + B ^ 2) *ᵥ v)
  have hBE1 : B * (1 + B + B ^ 2) = 1 + B + B ^ 2 := by
    calc B * (1 + B + B ^ 2) = B + B ^ 2 + B ^ 3 := by noncomm_ring
      _ = B + B ^ 2 + 1 := by rw [hB3]
      _ = 1 + B + B ^ 2 := by noncomm_ring
  rw [Matrix.mulVec_mulVec, hBE1, one_smul]

omit [Finite K] [CharP K 2] in
private theorem decomp_eig_omega (hS : RadSetup ε b ω) (v : Fin (2 * 2 + ε) → K) :
    (1 + ω ^ 2 • bMat b + ω • (bMat b) ^ 2) *ᵥ v ∈ eigSU b ω := by
  let B : Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) K := bMat b
  change (1 + ω ^ 2 • B + ω • B ^ 2) *ᵥ v ∈ eigSU b ω
  have hB3 : B ^ 3 = 1 := decomp_b_pow_three hS
  have hB2v : B *ᵥ (B *ᵥ v) = B ^ 2 *ᵥ v := by
    rw [pow_two, ← Matrix.mulVec_mulVec]
  have hB3v : B *ᵥ (B ^ 2 *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, ← pow_succ', hB3, Matrix.one_mulVec]
  rw [mem_eigSU]
  change B *ᵥ ((1 + ω ^ 2 • B + ω • B ^ 2) *ᵥ v) =
    ω • ((1 + ω ^ 2 • B + ω • B ^ 2) *ᵥ v)
  have hEomv : (1 + ω ^ 2 • B + ω • B ^ 2) *ᵥ v =
      v + ω ^ 2 • (B *ᵥ v) + ω • (B ^ 2 *ᵥ v) := by
    rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
      Matrix.smul_mulVec, Matrix.smul_mulVec]
  have hleft : B *ᵥ ((1 + ω ^ 2 • B + ω • B ^ 2) *ᵥ v) =
      B *ᵥ v + ω ^ 2 • (B ^ 2 *ᵥ v) + ω • v := by
    rw [hEomv, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul,
      Matrix.mulVec_smul, hB2v, hB3v]
  have hright : ω • ((1 + ω ^ 2 • B + ω • B ^ 2) *ᵥ v) =
      ω • v + B *ᵥ v + ω ^ 2 • (B ^ 2 *ᵥ v) := by
    rw [hEomv, smul_add, smul_add, smul_smul, smul_smul]
    have hω : ω * ω ^ 2 = 1 := by
      calc ω * ω ^ 2 = ω ^ 3 := by ring
        _ = 1 := hS.cube
    rw [hω, show ω * ω = ω ^ 2 by ring, one_smul]
  rw [hleft, hright]
  module

omit [Finite K] [CharP K 2] in
private theorem decomp_eig_omega_inv (hS : RadSetup ε b ω)
    (v : Fin (2 * 2 + ε) → K) :
    (1 + ω • bMat b + ω ^ 2 • (bMat b) ^ 2) *ᵥ v ∈ eigSU b ω⁻¹ := by
  let B : Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) K := bMat b
  change (1 + ω • B + ω ^ 2 • B ^ 2) *ᵥ v ∈ eigSU b ω⁻¹
  have hB3 : B ^ 3 = 1 := decomp_b_pow_three hS
  have hB2v : B *ᵥ (B *ᵥ v) = B ^ 2 *ᵥ v := by
    rw [pow_two, ← Matrix.mulVec_mulVec]
  have hB3v : B *ᵥ (B ^ 2 *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, ← pow_succ', hB3, Matrix.one_mulVec]
  rw [mem_eigSU, omega_inv_eq hS]
  change B *ᵥ ((1 + ω • B + ω ^ 2 • B ^ 2) *ᵥ v) =
    ω ^ 2 • ((1 + ω • B + ω ^ 2 • B ^ 2) *ᵥ v)
  have hEoiv : (1 + ω • B + ω ^ 2 • B ^ 2) *ᵥ v =
      v + ω • (B *ᵥ v) + ω ^ 2 • (B ^ 2 *ᵥ v) := by
    rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
      Matrix.smul_mulVec, Matrix.smul_mulVec]
  have hleft : B *ᵥ ((1 + ω • B + ω ^ 2 • B ^ 2) *ᵥ v) =
      B *ᵥ v + ω • (B ^ 2 *ᵥ v) + ω ^ 2 • v := by
    rw [hEoiv, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul,
      Matrix.mulVec_smul, hB2v, hB3v]
  have hright : ω ^ 2 • ((1 + ω • B + ω ^ 2 • B ^ 2) *ᵥ v) =
      ω ^ 2 • v + B *ᵥ v + ω • (B ^ 2 *ᵥ v) := by
    rw [hEoiv, smul_add, smul_add, smul_smul, smul_smul]
    have hω : ω ^ 2 * ω = 1 := by
      calc ω ^ 2 * ω = ω ^ 3 := by ring
        _ = 1 := hS.cube
    have hω2 : ω ^ 2 * ω ^ 2 = ω := by
      calc ω ^ 2 * ω ^ 2 = ω ^ 3 * ω := by ring
        _ = ω := by rw [hS.cube, one_mul]
    rw [hω, hω2, one_smul]
  rw [hleft, hright]
  module

omit [Finite K] [CharP K 2] in
private theorem decomp_mem {U : Submodule K (Fin (2 * 2 + ε) → K)}
    (hU : ∀ u ∈ U, bMat b *ᵥ u ∈ U) {v : Fin (2 * 2 + ε) → K} (hv : v ∈ U) :
    (1 + bMat b + (bMat b) ^ 2) *ᵥ v ∈ U ∧
    (1 + ω ^ 2 • bMat b + ω • (bMat b) ^ 2) *ᵥ v ∈ U ∧
    (1 + ω • bMat b + ω ^ 2 • (bMat b) ^ 2) *ᵥ v ∈ U := by
  let B : Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) K := bMat b
  change (1 + B + B ^ 2) *ᵥ v ∈ U ∧
    (1 + ω ^ 2 • B + ω • B ^ 2) *ᵥ v ∈ U ∧
    (1 + ω • B + ω ^ 2 • B ^ 2) *ᵥ v ∈ U
  have hB2v : B *ᵥ (B *ᵥ v) = B ^ 2 *ᵥ v := by
    rw [pow_two, ← Matrix.mulVec_mulVec]
  have hBv : B *ᵥ v ∈ U := hU v hv
  have hB2vU : B ^ 2 *ᵥ v ∈ U := by
    rw [← hB2v]
    exact hU (B *ᵥ v) hBv
  have hE1v : (1 + B + B ^ 2) *ᵥ v = v + B *ᵥ v + B ^ 2 *ᵥ v := by
    rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec]
  have hEomv : (1 + ω ^ 2 • B + ω • B ^ 2) *ᵥ v =
      v + ω ^ 2 • (B *ᵥ v) + ω • (B ^ 2 *ᵥ v) := by
    rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
      Matrix.smul_mulVec, Matrix.smul_mulVec]
  have hEoiv : (1 + ω • B + ω ^ 2 • B ^ 2) *ᵥ v =
      v + ω • (B *ᵥ v) + ω ^ 2 • (B ^ 2 *ᵥ v) := by
    rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
      Matrix.smul_mulVec, Matrix.smul_mulVec]
  refine ⟨?_, ?_, ?_⟩
  · rw [hE1v]
    exact U.add_mem (U.add_mem hv hBv) hB2vU
  · rw [hEomv]
    exact U.add_mem (U.add_mem hv (U.smul_mem _ hBv)) (U.smul_mem _ hB2vU)
  · rw [hEoiv]
    exact U.add_mem (U.add_mem hv (U.smul_mem _ hBv)) (U.smul_mem _ hB2vU)

omit [Finite K] in
private theorem decomp_matrix_sum (hS : RadSetup ε b ω) :
    (1 + bMat b + (bMat b) ^ 2) + (1 + ω ^ 2 • bMat b + ω • (bMat b) ^ 2) +
      (1 + ω • bMat b + ω ^ 2 • (bMat b) ^ 2) = 1 := by
  let B : Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) K := bMat b
  change (1 + B + B ^ 2) + (1 + ω ^ 2 • B + ω • B ^ 2) +
      (1 + ω • B + ω ^ 2 • B ^ 2) = 1
  rw [show (1 + B + B ^ 2) + (1 + ω ^ 2 • B + ω • B ^ 2) +
      (1 + ω • B + ω ^ 2 • B ^ 2) =
      (3 : K) • (1 : Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) K) +
        (1 + ω + ω ^ 2) • B + (1 + ω + ω ^ 2) • B ^ 2 by module]
  rw [one_add_omega_add_sq hS, three_eq_one]
  simp

omit [Finite K] in
private theorem decomp_sum_apply (hS : RadSetup ε b ω) (v : Fin (2 * 2 + ε) → K) :
    (1 + bMat b + (bMat b) ^ 2) *ᵥ v + (1 + ω ^ 2 • bMat b + ω • (bMat b) ^ 2) *ᵥ v +
      (1 + ω • bMat b + ω ^ 2 • (bMat b) ^ 2) *ᵥ v = v := by
  rw [← Matrix.add_mulVec, ← Matrix.add_mulVec, decomp_matrix_sum hS,
    Matrix.one_mulVec]

omit [Finite K] in
theorem RadSetup.decomp (hS : RadSetup ε b ω) {U : Submodule K (Fin (2 * 2 + ε) → K)}
    (hU : ∀ u ∈ U, ((b : GL (Fin (2 * 2 + ε)) K) : Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) K)
      *ᵥ u ∈ U) :
    ∀ v ∈ U, ∃ v₁ ∈ eigSU b 1 ⊓ U, ∃ w ∈ eigSU b ω ⊓ U, ∃ w' ∈ eigSU b ω⁻¹ ⊓ U,
      v = v₁ + w + w' := by
  intro v hv
  obtain ⟨hm1, hmω, hmωi⟩ := decomp_mem hU hv
  refine ⟨(1 + bMat b + (bMat b) ^ 2) *ᵥ v, ⟨decomp_eig_one hS v, hm1⟩,
    (1 + ω ^ 2 • bMat b + ω • (bMat b) ^ 2) *ᵥ v, ⟨decomp_eig_omega hS v, hmω⟩,
    (1 + ω • bMat b + ω ^ 2 • (bMat b) ^ 2) *ᵥ v,
      ⟨decomp_eig_omega_inv hS v, hmωi⟩, ?_⟩
  exact (decomp_sum_apply hS v).symm

omit [Finite K] [CharP K 2] in
theorem RadSetup.inf_eq_bot (hS : RadSetup ε b ω) : eigSU b ω ⊓ eigSU b ω⁻¹ = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro v hv
  rw [Submodule.mem_inf] at hv
  rw [Submodule.mem_bot]
  have hv1 : ((b : GL (Fin (2 * 2 + ε)) K) :
      Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) K) *ᵥ v = ω • v :=
    (mem_eigSU (y := b) (μ := ω)).mp hv.1
  have hv2 : ((b : GL (Fin (2 * 2 + ε)) K) :
      Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) K) *ᵥ v = ω⁻¹ • v :=
    (mem_eigSU (y := b) (μ := ω⁻¹)).mp hv.2
  have h : ω • v = ω⁻¹ • v := by rw [← hv1, hv2]
  have h' : (ω - ω⁻¹) • v = 0 := by
    rw [sub_smul, h, sub_self]
  exact (smul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr (omega_ne_inv hS))

omit [Finite K] in
theorem RadSetup.eq_zero_of_orth (hS : RadSetup ε b ω) (h : UnitaryFieldData 2 f K)
    {w' : Fin (2 * 2 + ε) → K} (hw' : w' ∈ eigSU b ω⁻¹)
    (horth : ∀ w ∈ eigSU b ω, stdHermForm h (2 * 2 + ε) w w' = 0) : w' = 0 := by
  have hzero : ∀ x, stdHermForm h (2 * 2 + ε) x w' = 0 := by
    intro x
    obtain ⟨v₁, hv₁, w, hw, w₂, hw₂, rfl⟩ :=
      hS.decomp (U := ⊤) (fun _ _ => Submodule.mem_top) x Submodule.mem_top
    have h1 : stdHermForm h (2 * 2 + ε) v₁ w' = 0 :=
      ((hS.symm.orth_one h) v₁ hv₁.1 w' hw').1
    have h2 : stdHermForm h (2 * 2 + ε) w w' = 0 := horth w hw.1
    have h3 : stdHermForm h (2 * 2 + ε) w₂ w' = 0 :=
      hS.symm.isotropic h w₂ hw₂.1 w' hw'
    simp only [LinearMap.add_apply, map_add, h1, h2, h3, add_zero]
  have hsym : ∀ y, stdHermForm h (2 * 2 + ε) w' y = 0 := by
    intro y
    have h' := (CFSG.LinearGroups.stdHermForm_isSymm h (2 * 2 + ε)).eq y w'
    rw [hzero y, map_zero] at h'
    exact h'.symm
  exact (CFSG.LinearGroups.stdHermForm_separatingLeft h (2 * 2 + ε)) w' hsym

omit [Finite K] [CharP K 2] in
theorem RadSetup.finrank_eig_one_le (hS : RadSetup ε b ω) :
    Module.finrank K (eigSU b 1) ≤ 1 := by
  let f : Module.End K (Fin (2 * 2 + ε) → K) :=
    Matrix.toLin' ((b : GL (Fin (2 * 2 + ε)) K) :
      Matrix (Fin (2 * 2 + ε)) (Fin (2 * 2 + ε)) K)
  have hInd : iSupIndep (fun μ : K => eigSU b μ) := by
    have h := Module.End.eigenspaces_iSupIndep f
    simpa [f, eigSU] using h
  have hd1 : Disjoint (eigSU b 1) (eigSU b ω) := by
    have h := (iSupIndep_def.mp hInd) 1
    have hle : eigSU b ω ≤ ⨆ j : K, ⨆ (_ : j ≠ 1), eigSU b j :=
      le_iSup₂ (f := fun j (_ : j ≠ 1) => eigSU b j) ω hS.ne_one
    exact Disjoint.mono_right hle h
  have hd2 : Disjoint (eigSU b ω⁻¹) (eigSU b 1 ⊔ eigSU b ω) := by
    have h := (iSupIndep_def.mp hInd) (ω⁻¹)
    have hle1 : eigSU b 1 ≤ ⨆ j : K, ⨆ (_ : j ≠ ω⁻¹), eigSU b j :=
      le_iSup₂ (f := fun j (_ : j ≠ ω⁻¹) => eigSU b j) 1
        (fun h => (inv_ne_one.mpr hS.ne_one) h.symm)
    have hleω : eigSU b ω ≤ ⨆ j : K, ⨆ (_ : j ≠ ω⁻¹), eigSU b j :=
      le_iSup₂ (f := fun j (_ : j ≠ ω⁻¹) => eigSU b j) ω (omega_ne_inv hS)
    exact Disjoint.mono_right (sup_le hle1 hleω) h
  have hsup1 : Module.finrank K ↥(eigSU b 1 ⊔ eigSU b ω) =
      Module.finrank K ↥(eigSU b 1) + Module.finrank K ↥(eigSU b ω) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (eigSU b 1) (eigSU b ω)
    rw [hd1.eq_bot, finrank_bot, add_zero] at h
    exact h
  have hsup2 : Module.finrank K ↥((eigSU b 1 ⊔ eigSU b ω) ⊔ eigSU b ω⁻¹) =
      Module.finrank K ↥(eigSU b 1 ⊔ eigSU b ω) + Module.finrank K ↥(eigSU b ω⁻¹) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq
      (eigSU b 1 ⊔ eigSU b ω) (eigSU b ω⁻¹)
    rw [inf_comm, hd2.eq_bot, finrank_bot, add_zero] at h
    exact h
  have hle : Module.finrank K ↥((eigSU b 1 ⊔ eigSU b ω) ⊔ eigSU b ω⁻¹) ≤ 2 * 2 + ε := by
    have h := Submodule.finrank_le (R := K) (M := Fin (2 * 2 + ε) → K)
      ((eigSU b 1 ⊔ eigSU b ω) ⊔ eigSU b ω⁻¹)
    rwa [Module.finrank_fin_fun] at h
  have hsum : Module.finrank K ↥((eigSU b 1 ⊔ eigSU b ω) ⊔ eigSU b ω⁻¹) =
      Module.finrank K ↥(eigSU b 1) + 4 := by
    rw [hsup2, hsup1, hS.finrank_eig, hS.finrank_eig_inv]
  rw [hsum] at hle
  have hε : ε ≤ 1 := hS.le_one
  omega

omit [Finite K] in
theorem RadSetup.eq_zero_of_isotropic_one (hS : RadSetup ε b ω) (h : UnitaryFieldData 2 f K)
    {v : Fin (2 * 2 + ε) → K} (hv : v ∈ eigSU b 1) (hvv : stdHermForm h (2 * 2 + ε) v v = 0) :
    v = 0 := by
  by_cases hv0 : v = 0
  · exact hv0
  · exfalso
    have hspan : K ∙ v ≤ eigSU b 1 := by
      rw [Submodule.span_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      simpa [hx] using hv
    have hfr_span : Module.finrank K ↥(K ∙ v) = 1 := finrank_span_singleton hv0
    have hle_span := Submodule.finrank_mono hspan
    have hle_one := hS.finrank_eig_one_le
    have hfr : Module.finrank K ↥(eigSU b 1) = 1 := by omega
    have hEq : eigSU b 1 = K ∙ v :=
      eq_span_singleton_of_mem_of_finrank_eq_one hfr hv hv0
    have horth : ∀ x, stdHermForm h (2 * 2 + ε) v x = 0 := by
      intro x
      obtain ⟨v₁, hv₁, w, hw, w₂, hw₂, rfl⟩ :=
        hS.decomp (U := ⊤) (fun _ _ => Submodule.mem_top) x Submodule.mem_top
      have hv₁_span : v₁ ∈ K ∙ v := by
        rw [← hEq]
        exact hv₁.1
      obtain ⟨c, hc⟩ := (Submodule.mem_span_singleton).mp hv₁_span
      have h1 : stdHermForm h (2 * 2 + ε) v v₁ = 0 := by
        rw [← hc, map_smul, smul_eq_mul, hvv, mul_zero]
      have h2 : stdHermForm h (2 * 2 + ε) v w = 0 := ((hS.orth_one h) v hv w hw.1).1
      have h3 : stdHermForm h (2 * 2 + ε) v w₂ = 0 :=
        ((hS.symm.orth_one h) v hv w₂ hw₂.1).1
      simp only [map_add, h1, h2, h3, add_zero]
    exact hv0 ((CFSG.LinearGroups.stdHermForm_separatingLeft h (2 * 2 + ε)) v horth)

omit [Finite K] in
theorem RadSetup.mem_of_isotropic_orth (hS : RadSetup ε b ω) (h : UnitaryFieldData 2 f K)
    {v : Fin (2 * 2 + ε) → K} (horth : ∀ w ∈ eigSU b ω, stdHermForm h (2 * 2 + ε) w v = 0)
    (hvv : stdHermForm h (2 * 2 + ε) v v = 0) : v ∈ eigSU b ω := by
  obtain ⟨v₁, hv₁, w, hw, w₂, hw₂, hv⟩ :=
    hS.decomp (U := ⊤) (fun _ _ => Submodule.mem_top) v Submodule.mem_top
  have hw2zero : w₂ = 0 := by
    refine hS.eq_zero_of_orth h hw₂.1 ?_
    intro w₀ hw₀
    have h1 : stdHermForm h (2 * 2 + ε) w₀ v₁ = 0 :=
      ((hS.orth_one h) v₁ hv₁.1 w₀ hw₀).2
    have h2 : stdHermForm h (2 * 2 + ε) w₀ w = 0 :=
      hS.isotropic h w₀ hw₀ w hw.1
    have h0 := horth w₀ hw₀
    rw [hv] at h0
    simp only [map_add, h1, h2, add_zero, zero_add] at h0
    exact h0
  have hv1zero : v₁ = 0 := by
    refine hS.eq_zero_of_isotropic_one h hv₁.1 ?_
    have h0 := hvv
    rw [hv, hw2zero, add_zero] at h0
    have h1 : stdHermForm h (2 * 2 + ε) v₁ w = 0 :=
      ((hS.orth_one h) v₁ hv₁.1 w hw.1).1
    have h2 : stdHermForm h (2 * 2 + ε) w v₁ = 0 :=
      ((hS.orth_one h) v₁ hv₁.1 w hw.1).2
    have h3 : stdHermForm h (2 * 2 + ε) w w = 0 := hS.isotropic h w hw.1 w hw.1
    simp only [LinearMap.add_apply, map_add, h1, h2, h3, add_zero] at h0
    exact h0
  have hwω := (mem_eigSU (y := b) (μ := ω)).mp hw.1
  rw [mem_eigSU]
  rw [hv, hv1zero, hw2zero]
  simpa using hwω

omit [Finite K] in
theorem RadSetup.mem_one_of_orth (hS : RadSetup ε b ω) (h : UnitaryFieldData 2 f K)
    {u : Fin (2 * 2 + ε) → K} (h₁ : ∀ w ∈ eigSU b ω, stdHermForm h (2 * 2 + ε) w u = 0)
    (h₂ : ∀ w ∈ eigSU b ω⁻¹, stdHermForm h (2 * 2 + ε) w u = 0) : u ∈ eigSU b 1 := by
  obtain ⟨v₁, hv₁, w, hw, w₂, hw₂, hu⟩ :=
    hS.decomp (U := ⊤) (fun _ _ => Submodule.mem_top) u Submodule.mem_top
  have hw2zero : w₂ = 0 := by
    refine hS.eq_zero_of_orth h hw₂.1 ?_
    intro w₀ hw₀
    have h1 : stdHermForm h (2 * 2 + ε) w₀ v₁ = 0 :=
      ((hS.orth_one h) v₁ hv₁.1 w₀ hw₀).2
    have h2 : stdHermForm h (2 * 2 + ε) w₀ w = 0 :=
      hS.isotropic h w₀ hw₀ w hw.1
    have h0 := h₁ w₀ hw₀
    rw [hu] at h0
    simp only [map_add, h1, h2, add_zero, zero_add] at h0
    exact h0
  have hwzero : w = 0 := by
    refine hS.symm.eq_zero_of_orth h ?_ ?_
    · rw [inv_inv]
      exact hw.1
    · intro w₀' hw₀'
      have h1 : stdHermForm h (2 * 2 + ε) w₀' v₁ = 0 :=
        ((hS.symm.orth_one h) v₁ hv₁.1 w₀' hw₀').2
      have h0 := h₂ w₀' hw₀'
      rw [hu, hw2zero, add_zero] at h0
      simp only [map_add, h1, zero_add] at h0
      exact h0
  simpa [hu, hwzero, hw2zero] using hv₁.1

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105
