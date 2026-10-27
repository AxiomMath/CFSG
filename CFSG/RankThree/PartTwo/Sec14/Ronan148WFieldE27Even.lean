module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148WFieldE27Odd

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open Matrix

variable {K : Type} [Field K]

namespace EvenE27

section Proj

variable {Y : Matrix (Fin 3) (Fin 3) K}

theorem mul_cubeProj_eq_smul (hY : Y * (Y * Y) = 1) {c : K} (hc : c ^ 3 = 1) :
    Y * cubeProj Y c = c ^ 2 • cubeProj Y c := by
  have h1 : c ^ 2 * c = 1 := by linear_combination hc
  have h2 : c ^ 2 * c ^ 2 = c := by linear_combination c * hc
  simp only [cubeProj, mul_add, mul_one, mul_smul_comm, hY, smul_add, smul_smul, h1, h2, one_smul]
  abel

theorem cubeProj_mul_cubeProj_eq_zero (hY : Y * (Y * Y) = 1) (hY' : Y * Y * Y = 1)
    {c c' : K} (hc : c ^ 3 = 1) (hc' : c' ^ 3 = 1) (hcc : c ^ 2 ≠ c' ^ 2) :
    cubeProj Y c * cubeProj Y c' = 0 := by
  have h1 : Y * (cubeProj Y c * cubeProj Y c') = c ^ 2 • (cubeProj Y c * cubeProj Y c') := by
    rw [← mul_assoc, mul_cubeProj_eq_smul hY hc, smul_mul_assoc]
  have h2 : Y * (cubeProj Y c * cubeProj Y c') = c' ^ 2 • (cubeProj Y c * cubeProj Y c') := by
    rw [← mul_assoc, cubeProj_comm, mul_assoc, mul_cubeProj_eq_smul hY hc', mul_smul_comm]
  have h3 : (c ^ 2 - c' ^ 2) • (cubeProj Y c * cubeProj Y c') = 0 := by
    rw [sub_smul, ← h1, ← h2, sub_self]
  exact (smul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hcc)

end Proj

theorem cubeProj_ne_one {y : GL (Fin 3) K} (hy3 : y ^ 3 = 1)
    (hys : y ∉ StatedScalars (Fin 3) K) {c : K} (hc : c ^ 3 = 1) :
    cubeProj (y : Matrix (Fin 3) (Fin 3) K) c ≠ 1 := by
  intro hP
  have hY : (y : Matrix (Fin 3) (Fin 3) K) * ((y : Matrix (Fin 3) (Fin 3) K) *
      (y : Matrix (Fin 3) (Fin 3) K)) = 1 := by
    have h := congrArg Units.val (show y * (y * y) = 1 from (pow_three y).symm.trans hy3)
    rwa [Units.val_mul, Units.val_mul, Units.val_one] at h
  have hc0 : c ≠ 0 := by
    rintro rfl
    norm_num at hc
  apply hys
  refine mem_statedScalars_of_eq_smul (a := c ^ 2) ?_ (pow_ne_zero 2 hc0)
  calc (y : Matrix (Fin 3) (Fin 3) K)
      = (y : Matrix (Fin 3) (Fin 3) K) * cubeProj (y : Matrix (Fin 3) (Fin 3) K) c := by
        rw [hP, mul_one]
    _ = c ^ 2 • cubeProj (y : Matrix (Fin 3) (Fin 3) K) c := mul_cubeProj_eq_smul hY hc
    _ = c ^ 2 • (1 : Matrix (Fin 3) (Fin 3) K) := by rw [hP]

theorem cubeProj_sum (Y : Matrix (Fin 3) (Fin 3) K) (h2 : (2 : K) = 0) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    cubeProj Y 1 + cubeProj Y τ + cubeProj Y (τ ^ 2) = 1 := by
  have hs1 : 1 + τ + τ ^ 2 = 0 := by
    have h : (τ - 1) * (1 + τ + τ ^ 2) = 0 := by linear_combination hτ
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hτ1)
  have hs2 : 1 + τ ^ 2 + (τ ^ 2) ^ 2 = 0 := by linear_combination hs1 + τ * hτ
  simp only [cubeProj]
  linear_combination (norm := module)
    h2 • (1 : Matrix (Fin 3) (Fin 3) K) + hs1 • Y + hs2 • (Y * Y)

theorem cube_root_facts {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    (1 : K) ^ 2 ≠ τ ^ 2 ∧ (1 : K) ^ 2 ≠ (τ ^ 2) ^ 2 ∧ τ ^ 2 ≠ (τ ^ 2) ^ 2 := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply hτ1
    linear_combination hτ + τ * h
  · intro h
    apply hτ1
    linear_combination (-τ) * hτ - h
  · intro h
    apply hτ1
    apply mul_left_cancel₀ hτ0
    linear_combination h + τ * hτ

theorem exists_pair {Y : Matrix (Fin 3) (Fin 3) K} (h2 : (2 : K) = 0)
    (hY : Y * (Y * Y) = 1) (hne1 : ∀ c : K, c ^ 3 = 1 → cubeProj Y c ≠ 1)
    {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {ψ : K ≃+* K} (hψτ : ψ τ = τ) :
    ∃ c c' : K, c ^ 3 = 1 ∧ c' ^ 3 = 1 ∧ c ^ 2 ≠ c' ^ 2 ∧ ψ c = c ∧ ψ c' = c' ∧
      cubeProj Y c ≠ 0 ∧ cubeProj Y c' ≠ 0 := by
  have hsum := cubeProj_sum Y h2 hτ hτ1
  obtain ⟨k1, k2, k3⟩ := cube_root_facts hτ hτ1
  have hτ2 : (τ ^ 2) ^ 3 = 1 := by linear_combination (τ ^ 3 + 1) * hτ
  have hψτ2 : ψ (τ ^ 2) = τ ^ 2 := by rw [map_pow, hψτ]
  have hψ1 : ψ 1 = 1 := map_one ψ
  have h1 : (1 : K) ^ 3 = 1 := one_pow 3
  by_cases hA : cubeProj Y 1 = 0 <;> by_cases hB : cubeProj Y τ = 0 <;>
    by_cases hC : cubeProj Y (τ ^ 2) = 0
  · simp [hA, hB, hC] at hsum
  · exact (hne1 (τ ^ 2) hτ2 (by simpa [hA, hB] using hsum)).elim
  · exact (hne1 τ hτ (by simpa [hA, hC] using hsum)).elim
  · exact ⟨τ, τ ^ 2, hτ, hτ2, k3, hψτ, hψτ2, hB, hC⟩
  · exact (hne1 1 h1 (by simpa [hB, hC] using hsum)).elim
  · exact ⟨1, τ ^ 2, h1, hτ2, k2, hψ1, hψτ2, hA, hC⟩
  · exact ⟨1, τ, h1, hτ, k1, hψ1, hψτ, hA, hB⟩
  · exact ⟨1, τ, h1, hτ, k1, hψ1, hψτ, hA, hB⟩

theorem mul_single_mul_apply (X P : Matrix (Fin 3) (Fin 3) K) (i j a b : Fin 3) :
    (X * Matrix.single i j (1 : K) * P) a b = X a i * P j b := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [Matrix.mul_single_apply_same, mul_one]
  · intro k _ hk
    rw [Matrix.mul_single_apply_of_ne (hbj := hk), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem single_map_eq {ψ : K ≃+* K} (i j : Fin 3) :
    (Matrix.single i j (1 : K)).map ψ = Matrix.single i j 1 := by
  ext a b
  simp only [Matrix.map_apply, Matrix.single_apply]
  split_ifs <;> simp

theorem exists_N {Y : Matrix (Fin 3) (Fin 3) K} (hY : Y * (Y * Y) = 1)
    (hY' : Y * Y * Y = 1) {c c' : K} (hc : c ^ 3 = 1) (hc' : c' ^ 3 = 1)
    (hcc : c ^ 2 ≠ c' ^ 2) (hPc : cubeProj Y c ≠ 0) (hPc' : cubeProj Y c' ≠ 0)
    {ψ : K ≃+* K} (hψc : ψ c = c) (hψc' : ψ c' = c') (hYψ : Y.map ψ = Y) :
    ∃ N : Matrix (Fin 3) (Fin 3) K, N ≠ 0 ∧ N * N = 0 ∧ Y * N = c ^ 2 • N ∧
      N * Y = c' ^ 2 • N ∧ N.map ψ = N := by
  obtain ⟨a₀, i₀, hai⟩ : ∃ a i : Fin 3, cubeProj Y c a i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hPc (Matrix.ext fun a i => by simpa using h a i)
  obtain ⟨j₀, b₀, hjb⟩ : ∃ j b : Fin 3, cubeProj Y c' j b ≠ 0 := by
    by_contra h
    push_neg at h
    exact hPc' (Matrix.ext fun a i => by simpa using h a i)
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin 3) (Fin 3) K,
      N = cubeProj Y c * Matrix.single i₀ j₀ 1 * cubeProj Y c' := ⟨_, rfl⟩
  have hentry : N a₀ b₀ = cubeProj Y c a₀ i₀ * cubeProj Y c' j₀ b₀ := by
    rw [hN]
    exact mul_single_mul_apply _ _ _ _ _ _
  have hPP : cubeProj Y c' * cubeProj Y c = 0 :=
    cubeProj_mul_cubeProj_eq_zero hY hY' hc' hc (Ne.symm hcc)
  refine ⟨N, ?_, ?_, ?_, ?_, ?_⟩
  · intro h0
    exact mul_ne_zero hai hjb (by rw [← hentry, h0, Matrix.zero_apply])
  · rw [hN]
    calc cubeProj Y c * Matrix.single i₀ j₀ 1 * cubeProj Y c' *
          (cubeProj Y c * Matrix.single i₀ j₀ 1 * cubeProj Y c')
        = cubeProj Y c * Matrix.single i₀ j₀ 1 * (cubeProj Y c' * cubeProj Y c) *
          (Matrix.single i₀ j₀ 1 * cubeProj Y c') := by simp only [mul_assoc]
      _ = 0 := by rw [hPP, mul_zero, zero_mul]
  · rw [hN]
    simp only [← mul_assoc]
    rw [mul_cubeProj_eq_smul hY hc, smul_mul_assoc, smul_mul_assoc]
  · rw [hN]
    simp only [mul_assoc]
    rw [← cubeProj_comm (Y := Y) (c := c'), mul_cubeProj_eq_smul hY hc', mul_smul_comm,
      mul_smul_comm]
  · rw [hN, Matrix.map_mul, Matrix.map_mul, cubeProj_map_fix hYψ hψc, cubeProj_map_fix hYψ hψc',
      single_map_eq]

theorem unip_mul (N : Matrix (Fin 3) (Fin 3) K) (hN : N * N = 0) (a b : K) :
    (1 + a • N) * (1 + b • N) = 1 + (a + b) • N := by
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hN, smul_zero,
    add_zero, add_smul]
  abel

theorem unip_sq (h2 : (2 : K) = 0) (N : Matrix (Fin 3) (Fin 3) K) (hN : N * N = 0) (a : K) :
    (1 + a • N) * (1 + a • N) = 1 := by
  have h : a + a = 0 := by rw [← two_mul, h2, zero_mul]
  rw [unip_mul N hN, h, zero_smul, add_zero]

@[expose] def unipSub (h2 : (2 : K) = 0) (N : Matrix (Fin 3) (Fin 3) K) (hN : N * N = 0) :
    Subgroup (GL (Fin 3) K) where
  carrier := {g | ∃ a : K, (g : Matrix (Fin 3) (Fin 3) K) = 1 + a • N}
  mul_mem' := by
    rintro g k ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b, by rw [Units.val_mul, ha, hb, unip_mul N hN]⟩
  one_mem' := ⟨0, by simp⟩
  inv_mem' := by
    rintro g ⟨a, ha⟩
    have hgg : g * g = 1 := Units.ext (by rw [Units.val_mul, ha, Units.val_one, unip_sq h2 N hN])
    exact ⟨a, by rw [inv_eq_of_mul_eq_one_right hgg]; exact ha⟩

@[expose] def unipElt (h2 : (2 : K) = 0) (N : Matrix (Fin 3) (Fin 3) K) (hN : N * N = 0)
    (a : K) : GL (Fin 3) K :=
  ⟨1 + a • N, 1 + a • N, unip_sq h2 N hN a, unip_sq h2 N hN a⟩

theorem unipElt_val (h2 : (2 : K) = 0) (N : Matrix (Fin 3) (Fin 3) K) (hN : N * N = 0)
    (a : K) : (unipElt h2 N hN a : Matrix (Fin 3) (Fin 3) K) = 1 + a • N :=
  rfl

theorem unipElt_mem (h2 : (2 : K) = 0) (N : Matrix (Fin 3) (Fin 3) K) (hN : N * N = 0)
    (a : K) : unipElt h2 N hN a ∈ unipSub h2 N hN :=
  ⟨a, rfl⟩

theorem unipSub_mul_self (h2 : (2 : K) = 0) (N : Matrix (Fin 3) (Fin 3) K) (hN : N * N = 0)
    {g : GL (Fin 3) K} (hg : g ∈ unipSub h2 N hN) : g * g = 1 := by
  obtain ⟨a, ha⟩ := hg
  exact Units.ext (by rw [Units.val_mul, ha, Units.val_one, unip_sq h2 N hN])

theorem unipSub_le_sl (h2 : (2 : K) = 0) (N : Matrix (Fin 3) (Fin 3) K) (hN : N * N = 0)
    (q : ℕ) : unipSub h2 N hN ≤ slPi true 3 q K := by
  intro g hg
  have hm : (g : Matrix (Fin 3) (Fin 3) K) * g = 1 := by
    have h := congrArg Units.val (unipSub_mul_self h2 N hN hg)
    rwa [Units.val_mul, Units.val_one] at h
  have hd : (g : Matrix (Fin 3) (Fin 3) K).det * (g : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [← Matrix.det_mul, hm, Matrix.det_one]
  have hsq : ((g : Matrix (Fin 3) (Fin 3) K).det - 1) *
      ((g : Matrix (Fin 3) (Fin 3) K).det - 1) = 0 := by
    linear_combination hd + (1 - (g : Matrix (Fin 3) (Fin 3) K).det) * h2
  rw [mem_slPi_true]
  exact sub_eq_zero.mp (mul_self_eq_zero.mp hsq)

theorem unipSub_frob (h2 : (2 : K) = 0) (N : Matrix (Fin 3) (Fin 3) K) (hN : N * N = 0)
    {ψ : K ≃+* K} (hNψ : N.map ψ = N) :
    ∀ u ∈ unipSub h2 N hN, frobGL ψ u ∈ unipSub h2 N hN := by
  rintro g ⟨a, ha⟩
  refine ⟨ψ a, ?_⟩
  rw [coe_frobGL, ha, Matrix.map_add _ (map_add ψ), Matrix.map_one _ (map_zero ψ) (map_one ψ),
    Matrix.map_smul' _ _ _ (map_mul ψ), hNψ]

theorem unipElt_not_scalar (h2 : (2 : K) = 0) (N : Matrix (Fin 3) (Fin 3) K)
    (hN : N * N = 0) (hN0 : N ≠ 0) : unipElt h2 N hN 1 ∉ StatedScalars (Fin 3) K := by
  rintro ⟨s, hs⟩
  have hmat : (unipElt h2 N hN 1 : Matrix (Fin 3) (Fin 3) K) = (s : K) • 1 := by
    rw [← hs, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have h' : (1 : Matrix (Fin 3) (Fin 3) K) + N = (s : K) • 1 := by
    rw [← hmat, unipElt_val, one_smul]
  have hN1 : N = ((s : K) - 1) • (1 : Matrix (Fin 3) (Fin 3) K) := by
    rw [sub_smul, one_smul, ← h']
    abel
  have hsq : ((s : K) - 1) • (1 : Matrix (Fin 3) (Fin 3) K) *
      (((s : K) - 1) • (1 : Matrix (Fin 3) (Fin 3) K)) = 0 := by
    rw [← hN1]
    exact hN
  have ht : ((s : K) - 1) * ((s : K) - 1) = 0 := by
    have h00 := congrFun (congrFun hsq 0) 0
    simpa [Matrix.mul_apply, Matrix.one_apply] using h00
  have ht0 : (s : K) - 1 = 0 := mul_self_eq_zero.mp ht
  exact hN0 (by rw [hN1, ht0, zero_smul])

theorem conj_formula {Y N : Matrix (Fin 3) (Fin 3) K} (hY : Y * (Y * Y) = 1) {c c' : K}
    (hc' : c' ^ 3 = 1) (hYN : Y * N = c ^ 2 • N) (hNY : N * Y = c' ^ 2 • N) (a : K) :
    Y * (1 + a • N) * (Y * Y) = 1 + (a * (c ^ 2 * c')) • N := by
  have hc4 : c' ^ 2 * c' ^ 2 = c' := by linear_combination c' * hc'
  have hNYY : N * (Y * Y) = c' • N := by
    rw [← mul_assoc, hNY, smul_mul_assoc, hNY, smul_smul, hc4]
  rw [mul_add, mul_one, mul_smul_comm, hYN, smul_smul, add_mul, smul_mul_assoc, hNYY, smul_smul,
    hY, mul_assoc a (c ^ 2) c']

end EvenE27

theorem exists_two_subgroup_of_cube_two {q : ℕ} (h2 : (2 : K) = 0)
    {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {ψ : K ≃+* K} (hψτ : ψ τ = τ)
    {y : GL (Fin 3) K} (hy3 : y ^ 3 = 1)
    (hys : y ∉ StatedScalars (Fin 3) K) (hyψ : frobGL ψ y = y) :
    ∃ U : Subgroup (GL (Fin 3) K), U ≤ slPi true 3 q K ∧ (∀ u ∈ U, u ^ 2 = 1) ∧
      (∃ u ∈ U, u ∉ StatedScalars (Fin 3) K) ∧ (∀ u ∈ U, frobGL ψ u ∈ U) ∧
      (∀ u ∈ U, y * u * y⁻¹ ∈ U) := by
  have hY : (y : Matrix (Fin 3) (Fin 3) K) * ((y : Matrix (Fin 3) (Fin 3) K) *
      (y : Matrix (Fin 3) (Fin 3) K)) = 1 := by
    have h := congrArg Units.val (show y * (y * y) = 1 from (pow_three y).symm.trans hy3)
    rwa [Units.val_mul, Units.val_mul, Units.val_one] at h
  have hY' : (y : Matrix (Fin 3) (Fin 3) K) * (y : Matrix (Fin 3) (Fin 3) K) *
      (y : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [mul_assoc]
    exact hY
  have hyinv : y⁻¹ = y * y :=
    inv_eq_of_mul_eq_one_right (show y * (y * y) = 1 from (pow_three y).symm.trans hy3)
  have hYψ : (y : Matrix (Fin 3) (Fin 3) K).map ψ = (y : Matrix (Fin 3) (Fin 3) K) := by
    rw [← coe_frobGL, hyψ]
  obtain ⟨c, c', hc, hc', hcc, hψc, hψc', hPc, hPc'⟩ :=
    EvenE27.exists_pair h2 hY (fun c hc => EvenE27.cubeProj_ne_one hy3 hys hc) hτ hτ1 hψτ
  obtain ⟨N, hN0, hNN, hYN, hNY, hNψ⟩ :=
    EvenE27.exists_N hY hY' hc hc' hcc hPc hPc' hψc hψc' hYψ
  refine ⟨EvenE27.unipSub h2 N hNN, EvenE27.unipSub_le_sl h2 N hNN q, ?_, ?_, ?_, ?_⟩
  · intro u hu
    rw [sq]
    exact EvenE27.unipSub_mul_self h2 N hNN hu
  · exact ⟨EvenE27.unipElt h2 N hNN 1, EvenE27.unipElt_mem h2 N hNN 1,
      EvenE27.unipElt_not_scalar h2 N hNN hN0⟩
  · exact EvenE27.unipSub_frob h2 N hNN hNψ
  · intro g hg
    obtain ⟨a, ha⟩ := hg
    refine ⟨a * (c ^ 2 * c'), ?_⟩
    rw [hyinv]
    simp only [Units.val_mul]
    rw [ha, EvenE27.conj_formula hY hc' hYN hNY a]

end CFSG.RankThree.PartTwo.Sec14.Ronan148W
