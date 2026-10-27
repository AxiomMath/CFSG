module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData

public section

namespace CFSG.LocalAnalysis.SteinbergCD

open Matrix

section Ring

variable {R : Type*} [Ring R]

theorem one_add_sq_of_add_self {N : R} (hN : N + N = 0) : (1 + N) ^ 2 = 1 + N ^ 2 := by
  calc (1 + N) ^ 2 = 1 + (N + N) + N ^ 2 := by noncomm_ring
    _ = 1 + N ^ 2 := by rw [hN, add_zero]

theorem one_add_pow_four_of_add_self {N : R} (hN : N + N = 0) (hN2 : N ^ 2 + N ^ 2 = 0) :
    (1 + N) ^ 4 = 1 + N ^ 4 := by
  rw [show 4 = 2 * 2 by norm_num, pow_mul, one_add_sq_of_add_self hN,
    one_add_sq_of_add_self hN2, ← pow_mul]

end Ring

theorem orderOf_mk_eq_four {G : Type*} [Group G] {Z : Subgroup G} [Z.Normal] {g : G}
    (h4 : g ^ 4 = 1) (h2 : g ^ 2 ∉ Z) : orderOf (g : G ⧸ Z) = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := (g : G ⧸ Z))
    (by
      rw [pow_one, ← QuotientGroup.mk_pow]
      intro hg
      exact h2 ((QuotientGroup.eq_one_iff _).1 hg))
    (by rw [← QuotientGroup.mk_pow, show 2 ^ (1 + 1) = 4 by norm_num, h4, QuotientGroup.mk_one])
  rw [h]
  norm_num

theorem orderOf_eq_four {G : Type*} [Group G] {g : G} (h4 : g ^ 4 = 1) (h2 : g ^ 2 ≠ 1) :
    orderOf g = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [orderOf_eq_prime_pow (p := 2) (n := 1) (by rwa [pow_one])
    (by rw [show 2 ^ (1 + 1) = 4 by norm_num, h4])]
  norm_num

variable {k : Type*} [Field k]

theorem eq_one_of_pow_four_eq_one (h2 : (2 : k) = 0) {x : k} (hx : x ^ 4 = 1) : x = 1 := by
  have h : (x - 1) ^ 4 = 0 := by
    linear_combination hx + (-2 * x ^ 3 + 3 * x ^ 2 - 2 * x + 1) * h2
  exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h)

theorem add_self_of_two_eq_zero (h2 : (2 : k) = 0) {n : Type*} (N : Matrix n n k) :
    N + N = 0 := by
  rw [← two_smul k N, h2, zero_smul]

theorem sq_eq_trace_smul_sub (M : Matrix (Fin 2) (Fin 2) k) :
    M ^ 2 = (M 0 0 + M 1 1) • M - M.det • (1 : Matrix (Fin 2) (Fin 2) k) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sq, mul_apply, Fin.sum_univ_two, det_fin_two] <;> ring

theorem sq_eq_zero_of_pow_four_eq_zero {M : Matrix (Fin 2) (Fin 2) k} (hM : M ^ 4 = 0) :
    M ^ 2 = 0 := by
  have hdet : M.det = 0 := by
    have h := congrArg Matrix.det hM
    rw [det_pow, Matrix.det_zero] at h
    exact pow_eq_zero_iff (by norm_num) |>.1 h
  set t := M 0 0 + M 1 1
  have h2 : M ^ 2 = t • M := by rw [sq_eq_trace_smul_sub, hdet, zero_smul, sub_zero]
  have h4 : M ^ 4 = (t ^ 3) • M := by
    rw [show 4 = 2 + 2 by norm_num, pow_add, h2, smul_mul_smul_comm, ← sq M, h2, smul_smul]
    congr 1
    ring
  rw [h4] at hM
  rcases smul_eq_zero.1 hM with ht | hM0
  · rw [h2, pow_eq_zero_iff (by norm_num) |>.1 ht, zero_smul]
  · rw [hM0, sq, mul_zero]

theorem SL_two_orderOf_ne_four (h2 : (2 : k) = 0) (A : SpecialLinearGroup (Fin 2) k) :
    orderOf A ≠ 4 := by
  intro hA
  have hA4 : (A : Matrix (Fin 2) (Fin 2) k) ^ 4 = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, ← hA, pow_orderOf_eq_one,
      Matrix.SpecialLinearGroup.coe_one]
  set M : Matrix (Fin 2) (Fin 2) k := (A : Matrix (Fin 2) (Fin 2) k) + 1
  have hMM := add_self_of_two_eq_zero h2 M
  have hM2 : M ^ 2 + M ^ 2 = 0 := add_self_of_two_eq_zero h2 _
  have hAM : (A : Matrix (Fin 2) (Fin 2) k) = 1 + M := by
    rw [add_comm 1 M, add_assoc, add_self_of_two_eq_zero h2, add_zero]
  have hM4 : M ^ 4 = 0 := by
    have h := one_add_pow_four_of_add_self hMM hM2
    rw [← hAM, hA4] at h
    have h' : (1 : Matrix (Fin 2) (Fin 2) k) + M ^ 4 = 1 + 0 := by rw [← h, add_zero]
    exact add_left_cancel h'
  have hsq : (A : Matrix (Fin 2) (Fin 2) k) ^ 2 = 1 := by
    rw [hAM, one_add_sq_of_add_self hMM, sq_eq_zero_of_pow_four_eq_zero hM4, add_zero]
  have hA2 : A ^ 2 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hsq, Matrix.SpecialLinearGroup.coe_one]
  have := orderOf_dvd_of_pow_eq_one hA2
  rw [hA] at this
  norm_num at this

section VecMulVec

variable {n : Type*} [Fintype n] [DecidableEq n]

abbrev bvec (i : n) : n → k := Pi.single i 1

theorem bvec_dot_bvec (i j : n) : bvec (k := k) i ⬝ᵥ bvec j = if i = j then 1 else 0 := by
  simp [bvec, Pi.single_apply, eq_comm]

omit [Fintype n] [DecidableEq n] in
theorem map_vecMulVec (φ : k →+* k) (a b : n → k) :
    (vecMulVec a b).map φ = vecMulVec (φ ∘ a) (φ ∘ b) := by
  ext i j
  simp [vecMulVec_apply]

omit [Fintype n] in
theorem comp_bvec (φ : k →+* k) (i : n) : (φ ∘ bvec i : n → k) = bvec i := by
  funext j
  simp only [Function.comp_apply, bvec, Pi.single_apply]
  split_ifs <;> simp

omit [Fintype n] in
theorem comp_bvec_add (φ : k →+* k) (i j : n) :
    (φ ∘ (bvec i + bvec j) : n → k) = bvec i + bvec j := by
  funext x
  simp only [Function.comp_apply, Pi.add_apply, map_add]
  rw [show φ (bvec i x) = (φ ∘ bvec i) x from rfl, show φ (bvec j x) = (φ ∘ bvec j) x from rfl,
    comp_bvec, comp_bvec]

end VecMulVec

section Linear

variable {d : ℕ}

@[expose] def linN (i₀ i₁ i₂ : Fin d) : Matrix (Fin d) (Fin d) k :=
  vecMulVec (bvec i₀) (bvec i₁) + vecMulVec (bvec i₁) (bvec i₂)

theorem linN_sq {i₀ i₁ i₂ : Fin d} (h01 : i₀ ≠ i₁) (h02 : i₀ ≠ i₂) (h12 : i₁ ≠ i₂) :
    linN (k := k) i₀ i₁ i₂ ^ 2 = vecMulVec (bvec i₀) (bvec i₂) := by
  rw [linN, sq]
  simp [add_mul, mul_add, vecMulVec_mul_vecMulVec, h01, h02, h12]

theorem linN_pow_four {i₀ i₁ i₂ : Fin d} (h01 : i₀ ≠ i₁) (h02 : i₀ ≠ i₂) (h12 : i₁ ≠ i₂) :
    linN (k := k) i₀ i₁ i₂ ^ 4 = 0 := by
  rw [show 4 = 2 * 2 by norm_num, pow_mul, linN_sq h01 h02 h12, sq, vecMulVec_mul_vecMulVec,
    bvec_dot_bvec]
  simp [Ne.symm h02]

theorem exists_orderOf_eq_four_projectiveSL (h2 : (2 : k) = 0) (hd : 3 ≤ d) :
    ∃ A : SpecialLinearGroup (Fin d) k, orderOf A = 4 ∧
      orderOf (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj d k A) = 4 := by
  set i₀ : Fin d := ⟨0, by omega⟩
  set i₁ : Fin d := ⟨1, by omega⟩
  set i₂ : Fin d := ⟨2, by omega⟩
  have h01 : i₀ ≠ i₁ := Fin.ne_of_val_ne (by simp [i₀, i₁])
  have h02 : i₀ ≠ i₂ := Fin.ne_of_val_ne (by simp [i₀, i₂])
  have h12 : i₁ ≠ i₂ := Fin.ne_of_val_ne (by simp [i₁, i₂])
  set N := linN (k := k) i₀ i₁ i₂
  have hN := add_self_of_two_eq_zero h2 N
  have hN2 : N ^ 2 + N ^ 2 = 0 := add_self_of_two_eq_zero h2 _
  have h4 : (1 + N) ^ 4 = 1 := by
    rw [one_add_pow_four_of_add_self hN hN2, linN_pow_four h01 h02 h12, add_zero]
  have hdet : (1 + N).det = 1 := by
    refine eq_one_of_pow_four_eq_one h2 ?_
    rw [← det_pow, h4, det_one]
  set A : SpecialLinearGroup (Fin d) k := ⟨1 + N, hdet⟩
  have hA4 : A ^ 4 = 1 := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
    exact h4)
  have hA2 : (A ^ 2 : SpecialLinearGroup (Fin d) k) = (1 + vecMulVec (bvec i₀) (bvec i₂) :
      Matrix (Fin d) (Fin d) k) := by
    rw [Matrix.SpecialLinearGroup.coe_pow]
    change (1 + N) ^ 2 = _
    rw [one_add_sq_of_add_self hN, linN_sq h01 h02 h12]
  have hnot : A ^ 2 ∉ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars d k := by
    rintro ⟨c, -, hc⟩
    have h := congrFun (congrFun hc i₀) i₂
    rw [hA2] at h
    simp [vecMulVec_apply, h02] at h
  refine ⟨A, orderOf_eq_four hA4 fun h => hnot (h ▸ one_mem _), orderOf_mk_eq_four hA4 hnot⟩

end Linear

section Unitary

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {f : ℕ} {F : Type} [Field F] {d : ℕ}

@[expose] def unitP (i₀ i₁ : Fin d) : Matrix (Fin d) (Fin d) F :=
  vecMulVec (bvec i₀ + bvec i₁) (bvec i₀ + bvec i₁)

@[expose] def unitR (i₀ i₁ i₂ : Fin d) : Matrix (Fin d) (Fin d) F :=
  vecMulVec (bvec i₀ + bvec i₁) (bvec i₂) + vecMulVec (bvec i₂) (bvec i₀ + bvec i₁)

section Products

variable {i₀ i₁ i₂ : Fin d} (h2 : (2 : F) = 0) (h01 : i₀ ≠ i₁) (h02 : i₀ ≠ i₂) (h12 : i₁ ≠ i₂)

include h2 h01 in
theorem u_dot_u : (bvec i₀ + bvec i₁ : Fin d → F) ⬝ᵥ (bvec i₀ + bvec i₁) = 0 := by
  simp only [add_dotProduct, dotProduct_add, bvec_dot_bvec, h01, Ne.symm h01, ↓reduceIte,
    add_zero, zero_add]
  linear_combination h2

include h02 h12 in
theorem u_dot_e : (bvec i₀ + bvec i₁ : Fin d → F) ⬝ᵥ bvec i₂ = 0 := by
  simp [h02, h12]

include h02 h12 in
theorem e_dot_u : (bvec i₂ : Fin d → F) ⬝ᵥ (bvec i₀ + bvec i₁) = 0 := by
  simp [dotProduct_add, Ne.symm h02, Ne.symm h12]

include h2 h01 in
theorem unitP_mul_unitP : unitP (F := F) i₀ i₁ * unitP i₀ i₁ = 0 := by
  rw [unitP, vecMulVec_mul_vecMulVec, u_dot_u h2 h01, zero_smul, vecMulVec_zero]

include h2 h01 h02 h12 in
theorem unitP_mul_unitR : unitP (F := F) i₀ i₁ * unitR i₀ i₁ i₂ = 0 := by
  simp only [unitP, unitR, mul_add, vecMulVec_mul_vecMulVec, u_dot_u h2 h01, u_dot_e h02 h12,
    zero_smul, vecMulVec_zero, add_zero]

include h2 h01 h02 h12 in
theorem unitR_mul_unitP : unitR (F := F) i₀ i₁ i₂ * unitP i₀ i₁ = 0 := by
  simp only [unitP, unitR, add_mul, vecMulVec_mul_vecMulVec, u_dot_u h2 h01, e_dot_u h02 h12,
    zero_smul, vecMulVec_zero, add_zero]

include h2 h01 h02 h12 in
theorem unitR_mul_unitR : unitR (F := F) i₀ i₁ i₂ * unitR i₀ i₁ i₂ = unitP i₀ i₁ := by
  simp only [unitP, unitR, add_mul, mul_add, vecMulVec_mul_vecMulVec, u_dot_u h2 h01,
    u_dot_e h02 h12, e_dot_u h02 h12, bvec_dot_bvec, ↓reduceIte, zero_smul, one_smul,
    vecMulVec_zero, zero_add, add_zero]

end Products

theorem exists_orderOf_eq_four_unitaryPSU (h : UnitaryFieldData 2 f F) (hd : 3 ≤ d) :
    ∃ T : unitarySU 2 f F d, orderOf T = 4 ∧ orderOf (unitaryProj h d T) = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.finite
  have : CharP F 2 := h.charP
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  set i₀ : Fin d := ⟨0, by omega⟩
  set i₁ : Fin d := ⟨1, by omega⟩
  set i₂ : Fin d := ⟨2, by omega⟩
  have h01 : i₀ ≠ i₁ := Fin.ne_of_val_ne (by simp [i₀, i₁])
  have h02 : i₀ ≠ i₂ := Fin.ne_of_val_ne (by simp [i₀, i₂])
  have h12 : i₁ ≠ i₂ := Fin.ne_of_val_ne (by simp [i₁, i₂])
  obtain ⟨c, hc⟩ := h.traceLin_surjective 1
  have hc' : c + h.bar c = 1 := by
    have := congrArg Subtype.val hc
    rwa [UnitaryFieldData.coe_traceLin] at this
  set P := unitP (F := F) i₀ i₁ with hPdef
  set R := unitR (F := F) i₀ i₁ i₂ with hRdef
  set N : Matrix (Fin d) (Fin d) F := c • P + R
  have hPP : P * P = 0 := unitP_mul_unitP h2 h01
  have hPR : P * R = 0 := unitP_mul_unitR h2 h01 h02 h12
  have hRP : R * P = 0 := unitR_mul_unitP h2 h01 h02 h12
  have hRR : R * R = P := unitR_mul_unitR h2 h01 h02 h12
  have hN2 : N ^ 2 = P := by
    rw [sq]
    simp only [N, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, hPP, hPR, hRP, hRR,
      smul_zero, zero_add]
  have hN4 : N ^ 4 = 0 := by rw [show 4 = 2 * 2 by norm_num, pow_mul, hN2, sq, hPP]
  have hNN := add_self_of_two_eq_zero h2 N
  have hNN2 : N ^ 2 + N ^ 2 = 0 := add_self_of_two_eq_zero h2 _
  have h4 : (1 + N) ^ 4 = 1 := by rw [one_add_pow_four_of_add_self hNN hNN2, hN4, add_zero]
  have hdet : (1 + N).det ≠ 0 := by
    have h1 : (1 + N).det = 1 := eq_one_of_pow_four_eq_one h2 (by rw [← det_pow, h4, det_one])
    rw [h1]
    exact one_ne_zero
  have hPbar : (P.map h.bar)ᵀ = P := by
    rw [hPdef, unitP, map_vecMulVec, transpose_vecMulVec, comp_bvec_add]
  have hRbar : (R.map h.bar)ᵀ = R := by
    rw [hRdef, unitR, Matrix.map_add _ (map_add h.bar), map_vecMulVec, map_vecMulVec,
      transpose_add, transpose_vecMulVec,
      transpose_vecMulVec]
    rw [comp_bvec_add, comp_bvec, add_comm]
  have hbar : ((1 + N).map h.bar)ᵀ = 1 + h.bar c • P + R := by
    have hsmul : (c • P).map h.bar = h.bar c • P.map h.bar := by
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
    rw [Matrix.map_add _ (map_add h.bar), Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_add _ (map_add h.bar), hsmul,
      transpose_add, transpose_add, transpose_one, transpose_smul, hPbar, hRbar, add_assoc]
  have hunit : ((1 + N).map h.bar)ᵀ * (1 + N) = 1 := by
    rw [hbar]
    simp only [N, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hPP, hPR,
      hRP, hRR, smul_zero, add_zero]
    have e : (1 : Matrix (Fin d) (Fin d) F) + h.bar c • P + R + (c • P + (R + P)) =
        1 + (c + h.bar c + 1) • P + (R + R) := by
      rw [add_smul, add_smul, one_smul]
      abel
    rw [e, hc', add_self_of_two_eq_zero h2 R, show (1 : F) + 1 = 2 by norm_num, h2, zero_smul,
      add_zero, add_zero]
  set T₀ : GL (Fin d) F := GeneralLinearGroup.mkOfDetNeZero (1 + N) hdet
  have hT₀ : (T₀ : Matrix (Fin d) (Fin d) F) = 1 + N := rfl
  have hmem : T₀ ∈ unitarySU 2 f F d := by
    rw [mem_unitarySU_iff h, hT₀]
    exact ⟨eq_one_of_pow_four_eq_one h2 (by rw [← det_pow, h4, det_one]), hunit⟩
  set T : unitarySU 2 f F d := ⟨T₀, hmem⟩
  have hT4 : T ^ 4 = 1 := Subtype.ext (Units.ext (by
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hT₀, h4, Subgroup.coe_one, Units.val_one]))
  have hT2 : (((T ^ 2 : unitarySU 2 f F d) : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
      1 + P := by
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hT₀, one_add_sq_of_add_self hNN, hN2]
  have hnot : T ^ 2 ∉ unitaryScalars h d := by
    intro hmem2
    obtain ⟨c', -, -, hc'⟩ := mem_unitaryScalars.1 hmem2
    have h1 := congrArg (fun g : GL (Fin d) F => (g : Matrix (Fin d) (Fin d) F) i₀ i₀) hc'
    have h3 := congrArg (fun g : GL (Fin d) F => (g : Matrix (Fin d) (Fin d) F) i₂ i₂) hc'
    simp only [hT2, GeneralLinearGroup.coe_scalar] at h1 h3
    simp [P, unitP, vecMulVec_apply, h01, Ne.symm h02, Ne.symm h12] at h1 h3
    rw [← h3, show (1 : F) + 1 = 2 by norm_num, h2] at h1
    exact one_ne_zero h1.symm
  exact ⟨T, orderOf_eq_four hT4 fun h' => hnot (h' ▸ one_mem _), orderOf_mk_eq_four hT4 hnot⟩

end Unitary

end CFSG.LocalAnalysis.SteinbergCD
