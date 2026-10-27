module

public import CFSG.RankThree.SubgroupLists.SymplecticPlusBlock
public import CFSG.RankThree.SubgroupLists.SymplecticSkewAxes
public import CFSG.RankThree.SubgroupLists.CliffordGeometry

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank Module

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K]

theorem fin_two_mul_self (M : Matrix (Fin 2) (Fin 2) K) :
    M * M = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

theorem sub_one_sq_commutator_of_common_eigvec {P P' Pi Pi' : Matrix (Fin 2) (Fin 2) K}
    (hP : Pi * P = 1) (hP' : Pi' * P' = 1) {v : Fin 2 → K} (hv : v ≠ 0) {α α' : K}
    (hPv : P *ᵥ v = α • v) (hP'v : P' *ᵥ v = α' • v) :
    (P * P' * Pi * Pi' - 1) * (P * P' * Pi * Pi' - 1) = 0 := by
  set C := P * P' * Pi * Pi' with hCdef
  have hdetPi : Pi.det * P.det = 1 := by rw [← Matrix.det_mul, hP, Matrix.det_one]
  have hdetPi' : Pi'.det * P'.det = 1 := by rw [← Matrix.det_mul, hP', Matrix.det_one]
  have hdetC : C.det = 1 := by
    rw [hCdef, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]
    linear_combination (Pi'.det * P'.det) * hdetPi + hdetPi'
  have hinv : ∀ {R Ri : Matrix (Fin 2) (Fin 2) K} {γ : K}, Ri * R = 1 → R *ᵥ v = γ • v →
      γ ≠ 0 ∧ Ri *ᵥ v = γ⁻¹ • v := by
    intro R Ri γ hR hRv
    have hback : v = Ri *ᵥ (R *ᵥ v) := by rw [Matrix.mulVec_mulVec, hR, Matrix.one_mulVec]
    rw [hRv, Matrix.mulVec_smul] at hback
    have hγ : γ ≠ 0 := by
      rintro rfl
      apply hv
      rw [hback, zero_smul]
    refine ⟨hγ, ?_⟩
    calc Ri *ᵥ v = γ⁻¹ • (γ • (Ri *ᵥ v)) := by rw [smul_smul, inv_mul_cancel₀ hγ, one_smul]
      _ = γ⁻¹ • v := by rw [← hback]
  obtain ⟨hα, hPiv⟩ := hinv hP hPv
  obtain ⟨hα', hPi'v⟩ := hinv hP' hP'v
  have h4 : P *ᵥ (P' *ᵥ (Pi *ᵥ (Pi' *ᵥ v))) = (α'⁻¹ * α⁻¹ * α' * α) • v := by
    rw [hPi'v, Matrix.mulVec_smul, hPiv, smul_smul, Matrix.mulVec_smul, hP'v, smul_smul,
      Matrix.mulVec_smul, hPv, smul_smul]
  have hCv : C *ᵥ v = v := by
    have e : α'⁻¹ * α⁻¹ * α' * α = 1 := by field_simp
    rw [hCdef, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h4, e,
      one_smul]
  have hdet1 : (C - 1).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp
      ⟨v, hv, by rw [Matrix.sub_mulVec, hCv, Matrix.one_mulVec, sub_self]⟩
  have htr : C.trace = 2 := by
    rw [Matrix.det_fin_two] at hdet1 hdetC
    rw [Matrix.trace_fin_two]
    simp only [Matrix.sub_apply, Matrix.one_apply_eq,
      Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
      Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), sub_zero] at hdet1
    linear_combination -hdet1 + hdetC
  have hCC := fin_two_mul_self C
  rw [htr, hdetC] at hCC
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_one, hCC, two_smul, one_smul]
  abel

theorem exists_common_eigvec {A : Matrix (Fin 2) (Fin 2) K} (hA : A ≠ 0) (hdet : A.det = 0) :
    ∃ v : Fin 2 → K, v ≠ 0 ∧ ∀ P Q : Matrix (Fin 2) (Fin 2) K, P * A = A * Q →
      ∃ α : K, P *ᵥ v = α • v := by
  rw [Matrix.det_fin_two] at hdet
  by_cases ha : A 0 0 = 0 ∧ A 1 0 = 0
  ·
    obtain ⟨ha0, ha1⟩ := ha
    refine ⟨![A 0 1, A 1 1], ?_, ?_⟩
    · intro h
      apply hA
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp at h0 h1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ha0, ha1, h0, h1]
    · intro P Q hPQ
      refine ⟨Q 1 1, ?_⟩
      ext i
      have := congrFun (congrFun hPQ i) 1
      simp only [Matrix.mul_apply, Fin.sum_univ_two] at this
      fin_cases i <;>
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, ha0, ha1] at this ⊢ <;>
        linear_combination this
  ·
    obtain ⟨μ, hμ0, hμ1⟩ : ∃ μ : K, A 0 1 = μ * A 0 0 ∧ A 1 1 = μ * A 1 0 := by
      by_cases h00 : A 0 0 = 0
      · have h10 : A 1 0 ≠ 0 := fun h => ha ⟨h00, h⟩
        have h01 : A 0 1 = 0 := by
          rw [h00, zero_mul] at hdet
          exact (mul_eq_zero.mp (by linear_combination -hdet)).resolve_right h10
        refine ⟨A 1 1 / A 1 0, by rw [h00, h01, mul_zero], ?_⟩
        field_simp
      · refine ⟨A 0 1 / A 0 0, by field_simp, ?_⟩
        field_simp
        linear_combination hdet
    refine ⟨![A 0 0, A 1 0], ?_, ?_⟩
    · intro h
      apply ha
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp at h0 h1
      exact ⟨h0, h1⟩
    · intro P Q hPQ
      refine ⟨Q 0 0 + μ * Q 1 0, ?_⟩
      ext i
      have := congrFun (congrFun hPQ i) 0
      simp only [Matrix.mul_apply, Fin.sum_univ_two] at this
      fin_cases i <;>
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this ⊢ <;>
        [rw [hμ0] at this; rw [hμ1] at this] <;>
        linear_combination this

@[expose] def offBlock (M : Matrix V₄ V₄ K) : Matrix (Fin 2) (Fin 2) K :=
  !![M (Sum.inl 0) (Sum.inl 1), M (Sum.inl 0) (Sum.inr 1);
    M (Sum.inr 0) (Sum.inl 1), M (Sum.inr 0) (Sum.inr 1)]

section Blocks

variable (h2 : (2 : K) ≠ 0)
include h2

theorem cross_zero_of_commute_tStd {X : Matrix V₄ V₄ K} (hX : X * tStdMat = tStdMat * X) :
    X (Sum.inl 0) (Sum.inl 1) = 0 ∧ X (Sum.inl 0) (Sum.inr 1) = 0 ∧
      X (Sum.inr 0) (Sum.inl 1) = 0 ∧ X (Sum.inr 0) (Sum.inr 1) = 0 ∧
      X (Sum.inl 1) (Sum.inl 0) = 0 ∧ X (Sum.inl 1) (Sum.inr 0) = 0 ∧
      X (Sum.inr 1) (Sum.inl 0) = 0 ∧ X (Sum.inr 1) (Sum.inr 0) = 0 := by
  have hne := one_ne_neg_one_of_two h2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply entry_eq_zero_of_commute_tStd h2 hX <;>
    simp only [stdSign_inl_zero, stdSign_inl_one, stdSign_inr_zero, stdSign_inr_one] <;>
    first | exact hne | exact hne.symm

theorem offBlock_mul_left {X R : Matrix V₄ V₄ K} (hX : X * tStdMat = tStdMat * X) :
    offBlock (X * R) = plusBlock X * offBlock R := by
  obtain ⟨z1, z2, z3, z4, -, -, -, -⟩ := cross_zero_of_commute_tStd h2 hX
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [offBlock, plusBlock, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, z1, z2,
      z3, z4]

theorem offBlock_mul_right {X R : Matrix V₄ V₄ K} (hX : X * tStdMat = tStdMat * X) :
    offBlock (R * X) = offBlock R * minusBlock X := by
  obtain ⟨z1, z2, z3, z4, -, -, -, -⟩ := cross_zero_of_commute_tStd h2 hX
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [offBlock, minusBlock, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, z1, z2,
      z3, z4]

theorem minusBlock_mul {X Y : Matrix V₄ V₄ K} (hX : X * tStdMat = tStdMat * X) :
    minusBlock (X * Y) = minusBlock X * minusBlock Y := by
  obtain ⟨-, -, -, -, z5, z6, z7, z8⟩ := cross_zero_of_commute_tStd h2 hX
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [minusBlock, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, z5, z6, z7, z8]

theorem plusBlock_mul_of_left {X Y : Matrix V₄ V₄ K} (hX : X * tStdMat = tStdMat * X) :
    plusBlock (X * Y) = plusBlock X * plusBlock Y := by
  obtain ⟨z1, z2, z3, z4, -, -, -, -⟩ := cross_zero_of_commute_tStd h2 hX
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [plusBlock, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, z1, z2, z3, z4]

end Blocks

theorem minusBlock_one : minusBlock (1 : Matrix V₄ V₄ K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [minusBlock, Matrix.one_apply]

theorem plusBlock_sub_one (M : Matrix V₄ V₄ K) : plusBlock (M - 1) = plusBlock M - 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [plusBlock, Matrix.one_apply]

theorem minusBlock_sub_one (M : Matrix V₄ V₄ K) : minusBlock (M - 1) = minusBlock M - 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [minusBlock, Matrix.one_apply]

theorem tStdMat_eq_cliffMat : (tStdMat : Matrix V₄ V₄ K) = cliffMat 1 0 0 0 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [tStdMat, stdSign, cliffMat, Matrix.diagonal]

theorem offBlock_of_isotropic (h2 : (2 : K) ≠ 0) {r : Matrix V₄ V₄ K}
    (hrM : r ∈ (cliffSpace : Submodule K _)) (hrt : cliffB tStdMat r = 0)
    (hrr : cliffB r r = 0) (hr0 : r ≠ 0) :
    offBlock r ≠ 0 ∧ (offBlock r).det = 0 := by
  have hr := eq_cliffMat_of_mem h2 hrM
  set x := r (Sum.inl 0) (Sum.inl 0)
  set y := r (Sum.inl 0) (Sum.inl 1)
  set z := r (Sum.inl 1) (Sum.inl 0)
  set b := r (Sum.inl 0) (Sum.inr 1)
  set c := r (Sum.inr 0) (Sum.inl 1)
  have hx : x = 0 := by
    have := hrt
    rw [tStdMat_eq_cliffMat, hr, cliffB_cliffMat h2] at this
    simpa using this
  have hq : y * z - b * c = 0 := by
    have := hrr
    rw [hr, cliffB_cliffMat h2, hx] at this
    have h22 : (2 : K)⁻¹ * 2 = 1 := inv_mul_cancel₀ h2
    linear_combination this - (y * z - b * c) * h22
  have hoff : offBlock r = !![y, b; c, z] := by
    rw [hr]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [offBlock, cliffMat]
  refine ⟨?_, ?_⟩
  · rw [hoff]
    intro h
    apply hr0
    have hy : y = 0 := by simpa using congrFun (congrFun h 0) 0
    have hb : b = 0 := by simpa using congrFun (congrFun h 0) 1
    have hc : c = 0 := by simpa using congrFun (congrFun h 1) 0
    have hz : z = 0 := by simpa using congrFun (congrFun h 1) 1
    rw [hr, hx, hy, hz, hb, hc]
    exact cliffMat_zero
  · rw [hoff, Matrix.det_fin_two_of]
    linear_combination hq

section Core

variable (h2 : (2 : K) ≠ 0)
include h2

omit h2 in
theorem mul_comm_tStd {A B : Matrix V₄ V₄ K} (hA : A * tStdMat = tStdMat * A)
    (hB : B * tStdMat = tStdMat * B) : A * B * tStdMat = tStdMat * (A * B) := by
  rw [Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hA, Matrix.mul_assoc]

omit h2 in
theorem inv_comm_tStd {z : GL V₄ K}
    (hz : (z : Matrix V₄ V₄ K) * tStdMat = tStdMat * (z : Matrix V₄ V₄ K)) :
    ((z⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * tStdMat =
      tStdMat * ((z⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) := by
  have h1 : ((z⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * (z : Matrix V₄ V₄ K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h1' : (z : Matrix V₄ V₄ K) * ((z⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc ((z⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * tStdMat
      = ((z⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * tStdMat * ((z : Matrix V₄ V₄ K) *
          ((z⁻¹ : GL V₄ K) : Matrix V₄ V₄ K)) := by rw [h1', Matrix.mul_one]
    _ = ((z⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * ((tStdMat * (z : Matrix V₄ V₄ K)) *
          ((z⁻¹ : GL V₄ K) : Matrix V₄ V₄ K)) := by simp only [Matrix.mul_assoc]
    _ = ((z⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * (((z : Matrix V₄ V₄ K) * tStdMat) *
          ((z⁻¹ : GL V₄ K) : Matrix V₄ V₄ K)) := by rw [hz]
    _ = tStdMat * ((z⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem plusBlock_commutator_sq_eq_zero {r : Matrix V₄ V₄ K}
    (hrM : r ∈ (cliffSpace : Submodule K _)) (hrt : cliffB tStdMat r = 0)
    (hrr : cliffB r r = 0) (hr0 : r ≠ 0) {x y : GL V₄ K}
    (hxt : (x : Matrix V₄ V₄ K) * tStdMat = tStdMat * (x : Matrix V₄ V₄ K))
    (hyt : (y : Matrix V₄ V₄ K) * tStdMat = tStdMat * (y : Matrix V₄ V₄ K))
    (hxr : (x : Matrix V₄ V₄ K) * r = r * (x : Matrix V₄ V₄ K))
    (hyr : (y : Matrix V₄ V₄ K) * r = r * (y : Matrix V₄ V₄ K)) :
    (plusBlock ((x * y * x⁻¹ * y⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) - 1) *
      (plusBlock ((x * y * x⁻¹ * y⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) - 1) = 0 := by
  obtain ⟨hA0, hAdet⟩ := offBlock_of_isotropic h2 hrM hrt hrr hr0
  obtain ⟨v, hv, hvP⟩ := exists_common_eigvec hA0 hAdet
  have hPA : ∀ z : GL V₄ K,
      (z : Matrix V₄ V₄ K) * tStdMat = tStdMat * (z : Matrix V₄ V₄ K) →
      (z : Matrix V₄ V₄ K) * r = r * (z : Matrix V₄ V₄ K) →
      plusBlock (z : Matrix V₄ V₄ K) * offBlock r = offBlock r * minusBlock
          (z : Matrix V₄ V₄ K) := by
    intro z hzt hzr
    rw [← offBlock_mul_left h2 hzt, ← offBlock_mul_right h2 hzt, hzr]
  obtain ⟨α, hα⟩ := hvP _ _ (hPA x hxt hxr)
  obtain ⟨α', hα'⟩ := hvP _ _ (hPA y hyt hyr)
  have hinvP : ∀ z : GL V₄ K,
      (z : Matrix V₄ V₄ K) * tStdMat = tStdMat * (z : Matrix V₄ V₄ K) →
      plusBlock ((z⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * plusBlock (z : Matrix V₄ V₄ K) = 1 := by
    intro z hzt
    rw [← plusBlock_mul_of_left h2 (inv_comm_tStd hzt), ← Units.val_mul, inv_mul_cancel,
      Units.val_one, plusBlock_one]
  have hxi := inv_comm_tStd hxt
  have hyi := inv_comm_tStd hyt
  have hc : plusBlock ((x * y * x⁻¹ * y⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) =
      plusBlock (x : Matrix V₄ V₄ K) * plusBlock (y : Matrix V₄ V₄ K) *
        plusBlock ((x⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) *
        plusBlock ((y⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) := by
    simp only [Units.val_mul]
    rw [plusBlock_mul_of_left h2 (mul_comm_tStd (mul_comm_tStd hxt hyt) hxi),
      plusBlock_mul_of_left h2 (mul_comm_tStd hxt hyt), plusBlock_mul_of_left h2 hxt]
  rw [hc]
  exact sub_one_sq_commutator_of_common_eigvec (hinvP x hxt) (hinvP y hyt) hv hα hα'

omit h2 in
theorem swap_conj_comm_tStd {X : Matrix V₄ V₄ K} (hX : X * tStdMat = tStdMat * X) :
    (swapMat * X * swapMat : Matrix V₄ V₄ K) * tStdMat =
      tStdMat * (swapMat * X * swapMat : Matrix V₄ V₄ K) := by
  have hS : (swapMat : Matrix V₄ V₄ K) * swapMat = 1 := swapMat_mul_self
  have hs : (swapMat : Matrix V₄ V₄ K) * tStdMat = -(tStdMat * swapMat) := by
    have h := congrArg (· * (swapMat : Matrix V₄ V₄ K)) (swap_conj_tStdMat (K := K))
    simp only [Matrix.mul_assoc, hS, Matrix.mul_one, Matrix.neg_mul] at h
    exact h
  calc (swapMat * X * swapMat : Matrix V₄ V₄ K) * tStdMat
      = swapMat * X * (swapMat * tStdMat) := by simp only [Matrix.mul_assoc]
    _ = -(swapMat * (X * tStdMat) * swapMat) := by
        rw [hs]
        simp only [Matrix.mul_neg, Matrix.mul_assoc]
    _ = -(swapMat * (tStdMat * X) * swapMat) := by rw [hX]
    _ = -((swapMat * tStdMat) * X * swapMat) := by simp only [Matrix.mul_assoc]
    _ = tStdMat * (swapMat * X * swapMat : Matrix V₄ V₄ K) := by
        rw [hs]
        simp only [Matrix.neg_mul, neg_neg, Matrix.mul_assoc]

theorem minusBlock_commutator_sq_eq_zero {r : Matrix V₄ V₄ K}
    (hrM : r ∈ (cliffSpace : Submodule K _)) (hrt : cliffB tStdMat r = 0)
    (hrr : cliffB r r = 0) (hr0 : r ≠ 0) {x y : GL V₄ K}
    (hxt : (x : Matrix V₄ V₄ K) * tStdMat = tStdMat * (x : Matrix V₄ V₄ K))
    (hyt : (y : Matrix V₄ V₄ K) * tStdMat = tStdMat * (y : Matrix V₄ V₄ K))
    (hxr : (x : Matrix V₄ V₄ K) * r = r * (x : Matrix V₄ V₄ K))
    (hyr : (y : Matrix V₄ V₄ K) * r = r * (y : Matrix V₄ V₄ K)) :
    (minusBlock ((x * y * x⁻¹ * y⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) - 1) *
      (minusBlock ((x * y * x⁻¹ * y⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) - 1) = 0 := by
  set σ : GL V₄ K := swapGL with hσ
  have hσm : ((σ : GL V₄ K) : Matrix V₄ V₄ K) = swapMat := coe_swapGL
  have hσi : ((σ⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) = swapMat := by rw [hσ, swapGL_inv, coe_swapGL]
  have hS : (swapMat : Matrix V₄ V₄ K) * swapMat = 1 := swapMat_mul_self
  have hconj : ∀ z : GL V₄ K, ((σ * z * σ⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) =
      swapMat * (z : Matrix V₄ V₄ K) * swapMat := by
    intro z
    rw [Units.val_mul, Units.val_mul, hσm, hσi]
  set r' : Matrix V₄ V₄ K := swapMat * r * swapMat with hr'
  have htM : (tStdMat : Matrix V₄ V₄ K) ∈ (cliffSpace : Submodule K _) := by
    rw [tStdMat_eq_cliffMat]
    exact cliffMat_mem _ _ _ _ _
  have hr'M : r' ∈ (cliffSpace : Submodule K _) := by
    have := conj_mem_cliffSpace (g := σ) swapGL_mem hrM
    rwa [hσm, hσi] at this
  have hr't : cliffB tStdMat r' = 0 := by
    have h := cliffB_conj h2 σ htM hrM
    rw [hσm, hσi, swap_conj_tStdMat, show -(tStdMat : Matrix V₄ V₄ K) = (-1 : K) • tStdMat by
      simp, cliffB_smul_left, hrt] at h
    have : cliffB tStdMat r' * (-1) = 0 := by rw [mul_comm]; exact h
    simpa using this
  have hr'r' : cliffB r' r' = 0 := by
    have h := cliffB_conj h2 σ hrM hrM
    rw [hσm, hσi, hrr] at h
    exact h
  have hr'0 : r' ≠ 0 := by
    intro h
    apply hr0
    calc r = swapMat * (swapMat * r * swapMat) * swapMat := by
          simp only [← Matrix.mul_assoc, hS, Matrix.one_mul]
          rw [Matrix.mul_assoc, hS, Matrix.mul_one]
      _ = 0 := by rw [← hr', h, Matrix.mul_zero, Matrix.zero_mul]
  have hzt : ∀ z : GL V₄ K, (z : Matrix V₄ V₄ K) * tStdMat = tStdMat * (z : Matrix V₄ V₄ K) →
      ((σ * z * σ⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * tStdMat =
        tStdMat * ((σ * z * σ⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) := by
    intro z hz
    rw [hconj]
    exact swap_conj_comm_tStd hz
  have hzr : ∀ z : GL V₄ K, (z : Matrix V₄ V₄ K) * r = r * (z : Matrix V₄ V₄ K) →
      ((σ * z * σ⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * r' = r' *
          ((σ * z * σ⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) := by
    intro z hz
    rw [hconj, hr']
    calc swapMat * (z : Matrix V₄ V₄ K) * swapMat * (swapMat * r * swapMat)
        = swapMat * ((z : Matrix V₄ V₄ K) * r) * swapMat := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (swapMat : Matrix V₄ V₄ K) swapMat, hS, Matrix.one_mul]
      _ = swapMat * (r * (z : Matrix V₄ V₄ K)) * swapMat := by rw [hz]
      _ = swapMat * r * swapMat * (swapMat * (z : Matrix V₄ V₄ K) * swapMat) := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (swapMat : Matrix V₄ V₄ K) swapMat, hS, Matrix.one_mul]
  have h := plusBlock_commutator_sq_eq_zero h2 hr'M hr't hr'r' hr'0 (hzt x hxt) (hzt y hyt)
    (hzr x hxr) (hzr y hyr)
  have e : σ * x * σ⁻¹ * (σ * y * σ⁻¹) * (σ * x * σ⁻¹)⁻¹ * (σ * y * σ⁻¹)⁻¹ =
      σ * (x * y * x⁻¹ * y⁻¹) * σ⁻¹ := by group
  rw [e, hconj, plusBlock_swap_conj] at h
  exact h

theorem commute_of_isotropic_tStd {G : Subgroup (GL V₄ K)}
    (hU0 : ∀ x ∈ G, IsSqZero x → x = 1) {r : Matrix V₄ V₄ K}
    (hrM : r ∈ (cliffSpace : Submodule K _)) (hrt : cliffB tStdMat r = 0)
    (hrr : cliffB r r = 0) (hr0 : r ≠ 0) {x y : GL V₄ K} (hxG : x ∈ G) (hyG : y ∈ G)
    (hxt : (x : Matrix V₄ V₄ K) * tStdMat = tStdMat * (x : Matrix V₄ V₄ K))
    (hyt : (y : Matrix V₄ V₄ K) * tStdMat = tStdMat * (y : Matrix V₄ V₄ K))
    (hxr : (x : Matrix V₄ V₄ K) * r = r * (x : Matrix V₄ V₄ K))
    (hyr : (y : Matrix V₄ V₄ K) * r = r * (y : Matrix V₄ V₄ K)) : x * y = y * x := by
  set c : GL V₄ K := x * y * x⁻¹ * y⁻¹ with hcdef
  have hct : (c : Matrix V₄ V₄ K) * tStdMat = tStdMat * (c : Matrix V₄ V₄ K) := by
    rw [hcdef, Units.val_mul, Units.val_mul, Units.val_mul]
    exact mul_comm_tStd (mul_comm_tStd (mul_comm_tStd hxt hyt) (inv_comm_tStd hxt))
      (inv_comm_tStd hyt)
  have hc1t : ((c : Matrix V₄ V₄ K) - 1) * tStdMat = tStdMat * ((c : Matrix V₄ V₄ K) - 1) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, hct, Matrix.one_mul, Matrix.mul_one]
  have hP := plusBlock_commutator_sq_eq_zero h2 hrM hrt hrr hr0 hxt hyt hxr hyr
  have hM := minusBlock_commutator_sq_eq_zero h2 hrM hrt hrr hr0 hxt hyt hxr hyr
  have hsq : IsSqZero c := by
    unfold IsSqZero
    have hN : ((c : Matrix V₄ V₄ K) - 1) * ((c : Matrix V₄ V₄ K) - 1) * tStdMat =
        tStdMat * (((c : Matrix V₄ V₄ K) - 1) * ((c : Matrix V₄ V₄ K) - 1)) :=
      mul_comm_tStd hc1t hc1t
    have hp : plusBlock (((c : Matrix V₄ V₄ K) - 1) * ((c : Matrix V₄ V₄ K) - 1)) =
        (0 : K) • 1 := by
      rw [plusBlock_mul_of_left h2 hc1t, plusBlock_sub_one, zero_smul]
      exact hP
    have hm : minusBlock (((c : Matrix V₄ V₄ K) - 1) * ((c : Matrix V₄ V₄ K) - 1)) =
        (0 : K) • 1 := by
      rw [minusBlock_mul h2 hc1t, minusBlock_sub_one, zero_smul]
      exact hM
    rw [eq_of_blocks h2 hN hp hm]
    simp
  have hc1 : c = 1 := hU0 c (by
    rw [hcdef]
    exact G.mul_mem (G.mul_mem (G.mul_mem hxG hyG) (G.inv_mem hxG)) (G.inv_mem hyG)) hsq
  calc x * y = c * (y * x) := by rw [hcdef]; group
    _ = y * x := by rw [hc1, one_mul]

end Core

end CFSG.RankThree.SubgroupLists
