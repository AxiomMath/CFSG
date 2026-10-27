module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiFrob

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open Matrix

variable {K : Type} [Field K] {p f : ℕ}

@[expose] def cubeProj (Y : Matrix (Fin 3) (Fin 3) K) (c : K) : Matrix (Fin 3) (Fin 3) K :=
  1 + c • Y + c ^ 2 • (Y * Y)

theorem matrix_map_smul {F : Type} [FunLike F K K] [RingHomClass F K K] (B : F) (c : K)
    (M : Matrix (Fin 3) (Fin 3) K) : (c • M).map B = B c • M.map B := by
  ext i j
  simp [Matrix.map_apply]

theorem cubeProj_comm {Y : Matrix (Fin 3) (Fin 3) K} {c : K} :
    Y * cubeProj Y c = cubeProj Y c * Y := by
  unfold cubeProj
  simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_assoc]

theorem cubeProj_smul_mul {Y : Matrix (Fin 3) (Fin 3) K} {c : K} (hY : Y * Y * Y = 1)
    (hc : c ^ 3 = 1) : (c • Y) * cubeProj Y c = cubeProj Y c := by
  have hY' : Y * (Y * Y) = 1 := by rw [← Matrix.mul_assoc]; exact hY
  unfold cubeProj
  simp only [mul_add, smul_mul_assoc, mul_smul_comm, Matrix.mul_one, smul_smul, Matrix.mul_assoc,
    hY']
  linear_combination (norm := module) hc • (1 : Matrix (Fin 3) (Fin 3) K)

theorem cubeProj_mul_smul {Y : Matrix (Fin 3) (Fin 3) K} {c : K} (hY : Y * Y * Y = 1)
    (hc : c ^ 3 = 1) : cubeProj Y c * (c • Y) = cubeProj Y c := by
  rw [mul_smul_comm, ← cubeProj_comm, ← smul_mul_assoc]
  exact cubeProj_smul_mul hY hc

theorem cubeProj_mul_self {Y : Matrix (Fin 3) (Fin 3) K} {c : K} (hY : Y * Y * Y = 1)
    (hc : c ^ 3 = 1) : cubeProj Y c * cubeProj Y c = (3 : K) • cubeProj Y c := by
  have h1 : cubeProj Y c * (c • Y) = cubeProj Y c := cubeProj_mul_smul hY hc
  have h2 : cubeProj Y c * (c ^ 2 • (Y * Y)) = cubeProj Y c := by
    have e : c ^ 2 • (Y * Y) = (c • Y) * (c • Y) := by
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul, sq]
    rw [e, ← Matrix.mul_assoc, h1, h1]
  have h3' : cubeProj Y c * cubeProj Y c = cubeProj Y c * (1 + c • Y + c ^ 2 • (Y * Y)) := rfl
  rw [h3', mul_add, mul_add, Matrix.mul_one, h1, h2]
  module

theorem cubeProj_sum {Y : Matrix (Fin 3) (Fin 3) K} {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    cubeProj Y 1 + cubeProj Y τ + cubeProj Y (τ ^ 2) =
      (3 : K) • (1 : Matrix (Fin 3) (Fin 3) K) := by
  have hs1 : 1 + τ + τ ^ 2 = 0 := by
    have h : (τ - 1) * (1 + τ + τ ^ 2) = 0 := by linear_combination hτ
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hτ1)
  have hs2 : 1 + τ ^ 2 + (τ ^ 2) ^ 2 = 0 := by linear_combination hs1 + τ * hτ
  unfold cubeProj
  linear_combination (norm := module) hs1 • Y + hs2 • (Y * Y)

theorem cubeProj_map_fix {ψ : K ≃+* K} {Y : Matrix (Fin 3) (Fin 3) K} {c : K}
    (hYψ : Y.map ψ = Y) (hψc : ψ c = c) : (cubeProj Y c).map ψ = cubeProj Y c := by
  unfold cubeProj
  rw [Matrix.map_add _ (map_add ψ), Matrix.map_add _ (map_add ψ),
    Matrix.map_one _ (map_zero ψ) (map_one ψ), matrix_map_smul, matrix_map_smul, Matrix.map_mul,
    map_pow,
    hψc, hYψ]

theorem cubeProj_bar {F : Type} [FunLike F K K] [RingHomClass F K K] (B : F)
    {Y : Matrix (Fin 3) (Fin 3) K} {c : K} (hY : Y * Y * Y = 1) (hc : c ^ 3 = 1)
    (hBc : B c = c ^ 2) (hYB : (Y.map B)ᵀ = Y * Y) :
    ((cubeProj Y c).map B)ᵀ = cubeProj Y c := by
  have h4 : (Y * Y) * (Y * Y) = Y := by
    calc (Y * Y) * (Y * Y) = Y * (Y * Y * Y) := by simp only [Matrix.mul_assoc]
      _ = Y := by rw [hY, Matrix.mul_one]
  have hc4 : (c ^ 2) ^ 2 = c := by linear_combination c * hc
  unfold cubeProj
  rw [Matrix.map_add _ (map_add B), Matrix.map_add _ (map_add B),
    Matrix.map_one _ (map_zero B) (map_one B), matrix_map_smul, matrix_map_smul, Matrix.map_mul,
    map_pow,
    hBc, Matrix.transpose_add, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul,
    Matrix.transpose_smul, Matrix.transpose_mul, hYB, hc4, h4]
  module

theorem exists_two_subgroup_of_cube_odd {π : Bool} (hπ : π = false → UnitaryFieldData p f K)
    (hq : π = false → ModThree false (p ^ f)) (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {ψ : K ≃+* K} (hψτ : ψ τ = τ)
    {y : GL (Fin 3) K} (hy : y ∈ glPi π 3 (p ^ f) K) (hy3 : y ^ 3 = 1)
    (hys : y ∉ StatedScalars (Fin 3) K) (hyψ : frobGL ψ y = y) :
    ∃ U : Subgroup (GL (Fin 3) K), U ≤ slPi π 3 (p ^ f) K ∧ (∀ u ∈ U, u ^ 2 = 1) ∧
      (∃ u ∈ U, u ∉ StatedScalars (Fin 3) K) ∧ (∀ u ∈ U, frobGL ψ u ∈ U) ∧
      (∀ u ∈ U, y * u * y⁻¹ ∈ U) := by
  have hY : (y : Matrix (Fin 3) (Fin 3) K) * (y : Matrix (Fin 3) (Fin 3) K) *
      (y : Matrix (Fin 3) (Fin 3) K) = 1 := by
    have h := congrArg Units.val hy3
    rw [Units.val_pow_eq_pow_val, Units.val_one, pow_three'] at h
    exact h
  have hYψ' : ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map ψ =
      (y : Matrix (Fin 3) (Fin 3) K) := by
    have h := congrArg Units.val hyψ
    rwa [coe_frobGL] at h
  set Y : Matrix (Fin 3) (Fin 3) K := (y : Matrix (Fin 3) (Fin 3) K) with hYdef
  have hex : ∃ c : K, c ^ 3 = 1 ∧ ψ c = c ∧ cubeProj Y c ≠ 0 := by
    by_contra hne
    push Not at hne
    have hsum := cubeProj_sum (Y := Y) hτ hτ1
    have e1 := hne 1 (one_pow 3) (map_one ψ)
    have e2 := hne τ hτ hψτ
    have e3 := hne (τ ^ 2) (by rw [← pow_mul, mul_comm, pow_mul, hτ, one_pow])
      (by rw [map_pow, hψτ])
    rw [e1, e2, e3, add_zero, add_zero] at hsum
    have h00 := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 0 0) hsum
    simp at h00
    exact h3 h00.symm
  obtain ⟨c, hc3, hψc, hPne⟩ := hex
  have hc0 : c ≠ 0 := by
    rintro rfl
    norm_num at hc3
  have hnot : ∀ a' : K, cubeProj Y c ≠ a' • (1 : Matrix (Fin 3) (Fin 3) K) := by
    intro a' hPa
    have ha' : a' ≠ 0 := by
      rintro rfl
      exact hPne (by rw [hPa, zero_smul])
    have h1 := cubeProj_smul_mul hY hc3
    rw [hPa, Matrix.mul_smul, Matrix.mul_one] at h1
    have h2' : c • Y = (1 : Matrix (Fin 3) (Fin 3) K) := by
      calc c • Y = a'⁻¹ • (a' • (c • Y)) := (inv_smul_smul₀ ha' _).symm
        _ = a'⁻¹ • (a' • (1 : Matrix (Fin 3) (Fin 3) K)) := by rw [h1]
        _ = 1 := inv_smul_smul₀ ha' _
    apply hys
    refine mem_statedScalars_of_eq_smul (a := c⁻¹) ?_ (inv_ne_zero hc0)
    calc (y : Matrix (Fin 3) (Fin 3) K) = c⁻¹ • (c • Y) := (inv_smul_smul₀ hc0 _).symm
      _ = c⁻¹ • (1 : Matrix (Fin 3) (Fin 3) K) := by rw [h2']
  obtain ⟨a, ha⟩ : ∃ a : K, a = 2 * 3⁻¹ := ⟨_, rfl⟩
  have ha3 : a * 3 = 2 := by rw [ha, mul_assoc, inv_mul_cancel₀ h3, mul_one]
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_mul] at ha3
    exact h2 ha3.symm
  have hsa : a * a * 3 = 2 * a := by rw [mul_assoc, ha3, mul_comm]
  have hψ2 : ψ 2 = 2 := map_ofNat ψ 2
  have hψ3 : ψ 3 = 3 := map_ofNat ψ 3
  have hψa : ψ a = a := by rw [ha, map_mul, map_inv₀, hψ2, hψ3]
  have hPP := cubeProj_mul_self hY hc3
  have hT₀T₀ : (a • cubeProj Y c - 1) * (a • cubeProj Y c - 1) = 1 := by
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_smul, Matrix.one_mul,
      Matrix.mul_one, hPP]
    linear_combination (norm := module) hsa • cubeProj Y c
  have hT₀Y : (a • cubeProj Y c - 1) * Y = Y * (a • cubeProj Y c - 1) := by
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, Matrix.one_mul, Matrix.mul_one,
      cubeProj_comm]
  have hψT₀ : (a • cubeProj Y c - 1).map ψ = a • cubeProj Y c - 1 := by
    rw [Matrix.map_sub _ (map_sub ψ), matrix_map_smul, hψa, cubeProj_map_fix hYψ' hψc,
      Matrix.map_one _ (map_zero ψ) (map_one ψ)]
  obtain ⟨d, hd⟩ : ∃ d : K, d = (a • cubeProj Y c - 1).det := ⟨_, rfl⟩
  have hdd : d * d = 1 := by
    rw [hd, ← Matrix.det_mul, hT₀T₀, Matrix.det_one]
  have hd1 : d = 1 ∨ d = -1 := mul_self_eq_one_iff.mp hdd
  have hψd : ψ d = d := by rcases hd1 with h' | h' <;> simp [h']
  obtain ⟨T, hTdef⟩ : ∃ T : Matrix (Fin 3) (Fin 3) K, T = d • (a • cubeProj Y c - 1) :=
    ⟨_, rfl⟩
  have hTT : T * T = 1 := by
    rw [hTdef]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, hT₀T₀, hdd, one_smul]
  have hdetT : T.det = 1 := by
    rw [hTdef, Matrix.det_smul, Fintype.card_fin, ← hd]
    linear_combination (d * d + 1) * hdd
  have hψT : T.map ψ = T := by
    rw [hTdef, matrix_map_smul, hψd, hψT₀]
  have hTY : T * Y = Y * T := by
    rw [hTdef]
    simp only [smul_mul_assoc, mul_smul_comm, hT₀Y]
  obtain ⟨t, ht⟩ : ∃ t : GL (Fin 3) K, (t : Matrix (Fin 3) (Fin 3) K) = T :=
    ⟨⟨T, T, hTT, hTT⟩, rfl⟩
  have hψt : frobGL ψ t = t := Units.ext (by rw [coe_frobGL, ht]; exact hψT)
  have hcomm : Commute y t :=
    Units.ext (by rw [Units.val_mul, Units.val_mul, ht]; exact hTY.symm)
  have ht2 : t ^ 2 = 1 :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one, sq, ht]; exact hTT)
  have htS : t ∈ slPi π 3 (p ^ f) K := by
    cases π with
    | false =>
      have h := hπ rfl
      have hq' := hq rfl
      rw [mem_slPi_false h]
      refine ⟨by rw [ht]; exact hdetT, ?_⟩
      have hBa : h.bar a = a := by
        rw [ha, map_mul, map_inv₀, map_ofNat h.bar 2, map_ofNat h.bar 3]
      have hBd : h.bar d = d := by rcases hd1 with h' | h' <;> simp [h']
      have hyB1 : (Y.map h.bar)ᵀ * Y = 1 := (mem_glPi_false h).mp hy
      have hYB : (Y.map h.bar)ᵀ = Y * Y := by
        calc (Y.map h.bar)ᵀ = (Y.map h.bar)ᵀ * (Y * Y * Y) := by rw [hY, Matrix.mul_one]
          _ = ((Y.map h.bar)ᵀ * Y) * (Y * Y) := by simp only [Matrix.mul_assoc]
          _ = Y * Y := by rw [hyB1, Matrix.one_mul]
      have hBc : h.bar c = c ^ 2 := by
        have e1 : c ^ (p ^ f) * c = 1 := by
          rw [← pow_succ]; exact pow_succ_eq_one_of_modThree hq' hc3
        have e2 : c ^ 2 * c = 1 := by rw [← pow_succ]; exact hc3
        rw [h.bar_apply]
        exact mul_right_cancel₀ hc0 (e1.trans e2.symm)
      have hT₀bar : ((a • cubeProj Y c - 1).map h.bar)ᵀ = a • cubeProj Y c - 1 := by
        rw [Matrix.map_sub _ (map_sub h.bar), matrix_map_smul, hBa,
          Matrix.map_one _ (map_zero h.bar) (map_one h.bar), Matrix.transpose_sub,
          Matrix.transpose_smul, Matrix.transpose_one, cubeProj_bar h.bar hY hc3 hBc hYB]
      have hTbar : (T.map h.bar)ᵀ = T := by
        rw [hTdef, matrix_map_smul, hBd, Matrix.transpose_smul, hT₀bar]
      rw [ht, hTbar]
      exact hTT
    | true =>
      rw [mem_slPi_true]
      rw [ht]
      exact hdetT
  have htn : t ∉ StatedScalars (Fin 3) K := by
    rintro ⟨u, hu⟩
    have hTu : T = (u : K) • (1 : Matrix (Fin 3) (Fin 3) K) := by
      have h' := congrArg Units.val hu
      rw [GeneralLinearGroup.coe_scalar, ht] at h'
      rw [← h', Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    have hT₀eq : a • cubeProj Y c - 1 = d • T := by
      rw [hTdef, smul_smul, hdd, one_smul]
    apply hnot (a⁻¹ * (d * u + 1))
    calc cubeProj Y c = a⁻¹ • (a • cubeProj Y c) := by rw [smul_smul, inv_mul_cancel₀ ha0, one_smul]
      _ = a⁻¹ • ((d * u) • (1 : Matrix (Fin 3) (Fin 3) K) + 1) := by
          rw [show a • cubeProj Y c = (a • cubeProj Y c - 1) + 1 from (sub_add_cancel _ _).symm,
            hT₀eq, hTu, smul_smul]
      _ = (a⁻¹ * (d * u + 1)) • (1 : Matrix (Fin 3) (Fin 3) K) := by module
  refine ⟨Subgroup.zpowers t, Subgroup.zpowers_le.mpr htS, ?_, ⟨t, Subgroup.mem_zpowers t, htn⟩,
    ?_, ?_⟩
  · intro u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    rw [← _root_.zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
      _root_.zpow_natCast, ht2, _root_.one_zpow]
  · intro u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    rw [map_zpow, hψt]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers t) k
  · intro u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    have hk : y * t ^ k = t ^ k * y := (hcomm.zpow_right k).eq
    rw [hk, mul_inv_cancel_right]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers t) k

end CFSG.RankThree.PartTwo.Sec14.Ronan148W
