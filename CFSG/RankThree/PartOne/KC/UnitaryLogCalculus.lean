module

public import CFSG.RankThree.GroupTheory.SteinbergCETruncatedExpLog
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeForm

public section

namespace CFSG.RankThree.PartOne

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.GroupTheory

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ}

@[expose] noncomputable def unitaryAdjoint (h : UnitaryFieldData p f K) (C : GL (Fin n) K)
    (M : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K :=
  (↑(C⁻¹) : Matrix (Fin n) (Fin n) K) * (M.map h.bar)ᵀ * (C : Matrix (Fin n) (Fin n) K)

namespace KCUnitaryLog

variable (h : UnitaryFieldData p f K) (C : GL (Fin n) K)

theorem coe_mul_inv : (C : Matrix (Fin n) (Fin n) K) * (↑(C⁻¹) : Matrix (Fin n) (Fin n) K) = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem coe_inv_mul : (↑(C⁻¹) : Matrix (Fin n) (Fin n) K) * (C : Matrix (Fin n) (Fin n) K) = 1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

theorem unitaryAdjoint_mul (M N : Matrix (Fin n) (Fin n) K) :
    unitaryAdjoint h C (M * N) = unitaryAdjoint h C N * unitaryAdjoint h C M := by
  unfold unitaryAdjoint
  rw [Matrix.map_mul, Matrix.transpose_mul]
  calc _ = (↑(C⁻¹) : Matrix (Fin n) (Fin n) K) * (N.map h.bar)ᵀ *
        ((C : Matrix (Fin n) (Fin n) K) * (↑(C⁻¹) : Matrix (Fin n) (Fin n) K)) *
          (M.map h.bar)ᵀ * (C : Matrix (Fin n) (Fin n) K) := by
        rw [coe_mul_inv, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem unitaryAdjoint_one : unitaryAdjoint h C (1 : Matrix (Fin n) (Fin n) K) = 1 := by
  unfold unitaryAdjoint
  rw [Matrix.map_one _ (map_zero h.bar) (map_one h.bar), Matrix.transpose_one, Matrix.mul_one,
    coe_inv_mul]

theorem unitaryAdjoint_add (M N : Matrix (Fin n) (Fin n) K) :
    unitaryAdjoint h C (M + N) = unitaryAdjoint h C M + unitaryAdjoint h C N := by
  unfold unitaryAdjoint
  rw [Matrix.map_add _ (map_add h.bar), Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]

theorem unitaryAdjoint_neg (M : Matrix (Fin n) (Fin n) K) :
    unitaryAdjoint h C (-M) = -unitaryAdjoint h C M := by
  unfold unitaryAdjoint
  rw [show (-M).map h.bar = -(M.map h.bar) from Matrix.map_neg _ (map_neg h.bar) M,
    Matrix.transpose_neg, Matrix.mul_neg, Matrix.neg_mul]

theorem unitaryAdjoint_sub (M N : Matrix (Fin n) (Fin n) K) :
    unitaryAdjoint h C (M - N) = unitaryAdjoint h C M - unitaryAdjoint h C N := by
  rw [sub_eq_add_neg, unitaryAdjoint_add, unitaryAdjoint_neg, ← sub_eq_add_neg]

theorem unitaryAdjoint_smul (c : K) (M : Matrix (Fin n) (Fin n) K) :
    unitaryAdjoint h C (c • M) = h.bar c • unitaryAdjoint h C M := by
  unfold unitaryAdjoint
  rw [Matrix.map_smul' _ c M (map_mul h.bar), Matrix.transpose_smul, Matrix.mul_smul,
    Matrix.smul_mul]

theorem unitaryAdjoint_pow (M : Matrix (Fin n) (Fin n) K) (k : ℕ) :
    unitaryAdjoint h C (M ^ k) = unitaryAdjoint h C M ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, unitaryAdjoint_one]
  | succ k ih => rw [pow_succ, unitaryAdjoint_mul, ih, pow_succ']

theorem unitaryAdjoint_sum {ι : Type*} (s : Finset ι) (F : ι → Matrix (Fin n) (Fin n) K) :
    unitaryAdjoint h C (∑ i ∈ s, F i) = ∑ i ∈ s, unitaryAdjoint h C (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    unfold unitaryAdjoint
    rw [Matrix.map_zero _ (map_zero h.bar), Matrix.transpose_zero, Matrix.mul_zero,
      Matrix.zero_mul]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, unitaryAdjoint_add, ih]


include h in
theorem hK_of_le (hnp : n ≤ p) : ∀ m : ℕ, 0 < m → m < n → (m : K) ≠ 0 := by
  intro m hm hmn hcast
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  exact Nat.not_dvd_of_pos_of_lt hm (by omega) ((CharP.cast_eq_zero_iff K p m).mp hcast)

theorem unitaryAdjoint_truncExp (N : Matrix (Fin n) (Fin n) K) :
    unitaryAdjoint h C (truncExp n N) = truncExp n (unitaryAdjoint h C N) := by
  unfold unitaryAdjoint
  rw [← truncExp_map (h.bar : K →+* K) N]
  exact dagger_truncExp C (N.map h.bar)

theorem unitaryAdjoint_truncLog (u : Matrix (Fin n) (Fin n) K) :
    unitaryAdjoint h C (truncLog n u) = truncLog n (unitaryAdjoint h C u) := by
  unfold unitaryAdjoint
  rw [← truncLog_map (h.bar : K →+* K) u]
  exact dagger_truncLog C (u.map h.bar)

theorem det_one_add_of_isNilpotent {R : Matrix (Fin n) (Fin n) K} (hR : IsNilpotent R) :
    (1 + R).det = 1 := by
  have h1 : (-R).charpoly = Polynomial.X ^ Fintype.card (Fin n) :=
    sub_eq_zero.mp (Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hR.neg).eq_zero
  have h2 := Matrix.eval_charpoly (-R) 1
  rw [h1, Polynomial.eval_pow, Polynomial.eval_X, one_pow, map_one] at h2
  rw [sub_neg_eq_add] at h2
  exact h2.symm

theorem barTranspose_truncExp_mul (hn : 1 ≤ n) (hnp : n ≤ p) {N : Matrix (Fin n) (Fin n) K}
    (hN : N ^ n = 0) (hskew : unitaryAdjoint h C N = -N) :
    ((truncExp n N).map h.bar)ᵀ * (C : Matrix (Fin n) (Fin n) K) * truncExp n N =
      (C : Matrix (Fin n) (Fin n) K) := by
  have h1 : unitaryAdjoint h C (truncExp n N) = truncExp n (-N) := by
    rw [unitaryAdjoint_truncExp, hskew]
  have h2 : ((truncExp n N).map h.bar)ᵀ * (C : Matrix (Fin n) (Fin n) K) =
      (C : Matrix (Fin n) (Fin n) K) * truncExp n (-N) := by
    rw [← h1]
    unfold unitaryAdjoint
    calc ((truncExp n N).map h.bar)ᵀ * (C : Matrix (Fin n) (Fin n) K) =
          ((C : Matrix (Fin n) (Fin n) K) * (↑(C⁻¹) : Matrix (Fin n) (Fin n) K)) *
            ((truncExp n N).map h.bar)ᵀ * (C : Matrix (Fin n) (Fin n) K) := by
          rw [coe_mul_inv, Matrix.one_mul]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [h2, Matrix.mul_assoc, truncExp_neg_mul_truncExp hn (hK_of_le h hnp) hN, Matrix.mul_one]

theorem det_truncExp (hn : 1 ≤ n) {N : Matrix (Fin n) (Fin n) K} (hN : N ^ n = 0) :
    (truncExp n N).det = 1 := by
  have h1 : IsNilpotent (truncExp n N - 1) := ⟨n, truncExp_sub_one_pow hn hN⟩
  have := det_one_add_of_isNilpotent h1
  rwa [add_sub_cancel] at this

include h in
@[expose] noncomputable def truncExpUnit (hn : 1 ≤ n) (hnp : n ≤ p)
    {N : Matrix (Fin n) (Fin n) K} (hN : N ^ n = 0) : GL (Fin n) K :=
  ⟨truncExp n N, truncExp n (-N),
    by
      have hN' : (-N) ^ n = 0 := by rw [neg_pow, hN, mul_zero]
      have := truncExp_neg_mul_truncExp hn (hK_of_le h hnp) hN'
      rwa [neg_neg] at this,
    truncExp_neg_mul_truncExp hn (hK_of_le h hnp) hN⟩


theorem unitaryAdjoint_truncLog_of_mem (hn : 1 ≤ n) (hnp : n ≤ p) {g : GL (Fin n) K}
    (hg : g ∈ gramSU h (C : Matrix (Fin n) (Fin n) K))
    (hu : IsNilpotent ((g : Matrix (Fin n) (Fin n) K) - 1)) :
    IsNilpotent (truncLog n (g : Matrix (Fin n) (Fin n) K)) ∧
      unitaryAdjoint h C (truncLog n (g : Matrix (Fin n) (Fin n) K)) =
        -truncLog n (g : Matrix (Fin n) (Fin n) K) := by
  set u : Matrix (Fin n) (Fin n) K := (g : Matrix (Fin n) (Fin n) K) with hu_def
  have hu' : (u - 1) ^ n = 0 := matrix_pow_eq_zero_of_isNilpotent hu
  have hK := hK_of_le h hnp
  set N := truncLog n u with hN
  have hN' : N ^ n = 0 := truncLog_pow hu'
  refine ⟨⟨n, hN'⟩, ?_⟩
  have hexp : truncExp n N = u := truncExp_truncLog hn hK hu'
  have hdag1 : unitaryAdjoint h C u * u = 1 := by
    have hgC : (u.map h.bar)ᵀ * (C : Matrix (Fin n) (Fin n) K) * u = C := (mem_gramSU.mp hg).1
    unfold unitaryAdjoint
    calc (↑(C⁻¹) : Matrix (Fin n) (Fin n) K) * (u.map h.bar)ᵀ * (C : Matrix (Fin n) (Fin n) K) * u
        = (↑(C⁻¹) : Matrix (Fin n) (Fin n) K) *
            ((u.map h.bar)ᵀ * (C : Matrix (Fin n) (Fin n) K) * u) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hgC]; exact coe_inv_mul C
  have hinv : truncExp n (-N) * u = 1 := by
    rw [← hexp]
    exact truncExp_neg_mul_truncExp hn hK hN'
  have hdag : unitaryAdjoint h C u = truncExp n (-N) := by
    have h2 : u * truncExp n (-N) = 1 := mul_eq_one_comm.mp hinv
    calc unitaryAdjoint h C u = unitaryAdjoint h C u * (u * truncExp n (-N)) := by
          rw [h2, Matrix.mul_one]
      _ = truncExp n (-N) := by rw [← Matrix.mul_assoc, hdag1, Matrix.one_mul]
  have hneg : (-N) ^ n = 0 := by rw [neg_pow, hN', mul_zero]
  rw [unitaryAdjoint_truncLog, hdag, truncLog_truncExp hn hK hneg]

theorem unitaryAdjoint_map (hC : IsPrimeFormGram C) (σ : K ≃+* K)
    (M : Matrix (Fin n) (Fin n) K) :
    unitaryAdjoint h C (M.map σ) = (unitaryAdjoint h C M).map σ := by
  unfold unitaryAdjoint
  have hCσ : (C : Matrix (Fin n) (Fin n) K).map σ = C := hC.map_eq_ringEquiv σ
  have hCinv : (↑(C⁻¹) : Matrix (Fin n) (Fin n) K).map σ = ↑(C⁻¹) := by
    have h1 : (↑(C⁻¹) : Matrix (Fin n) (Fin n) K).map σ * (C : Matrix (Fin n) (Fin n) K) = 1 := by
      conv_lhs => rw [← hCσ]
      rw [← Matrix.map_mul, coe_inv_mul, Matrix.map_one _ (map_zero σ) (map_one σ)]
    calc (↑(C⁻¹) : Matrix (Fin n) (Fin n) K).map σ =
        (↑(C⁻¹) : Matrix (Fin n) (Fin n) K).map σ * (C * ↑(C⁻¹)) := by
          rw [coe_mul_inv, Matrix.mul_one]
      _ = ↑(C⁻¹) := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hcomm : (M.map σ).map h.bar = (M.map h.bar).map σ := by
    ext i j
    simp [map_bar_comm h σ]
  rw [hcomm, Matrix.map_mul, Matrix.map_mul, hCσ, hCinv, Matrix.transpose_map]

end KCUnitaryLog


@[expose] noncomputable def unitaryExp (h : UnitaryFieldData p f K) {C : GL (Fin n) K}
    (hn : 3 ≤ n) (hnp : n ≤ p) {N : Matrix (Fin n) (Fin n) K} (hN : N ^ n = 0)
    (hskew : unitaryAdjoint h C N = -N) : gramSU h (C : Matrix (Fin n) (Fin n) K) :=
  ⟨KCUnitaryLog.truncExpUnit h (by omega) hnp hN, mem_gramSU.mpr
    ⟨KCUnitaryLog.barTranspose_truncExp_mul h C (by omega) hnp hN hskew,
      KCUnitaryLog.det_truncExp (by omega) hN⟩⟩

theorem coe_unitaryExp (h : UnitaryFieldData p f K) {C : GL (Fin n) K} (hn : 3 ≤ n) (hnp : n ≤ p)
    {N : Matrix (Fin n) (Fin n) K} (hN : N ^ n = 0) (hskew : unitaryAdjoint h C N = -N) :
    (((unitaryExp h hn hnp hN hskew : gramSU h (C : Matrix (Fin n) (Fin n) K)) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = truncExp n N :=
  rfl

theorem unitary_small_unipotent_logarithm_calculus (h : UnitaryFieldData p f K) (_hp3 : 3 < p)
    (hn3 : 3 ≤ n) (hnp : n ≤ p) {C : GL (Fin n) K} (hC : IsPrimeFormGram C) :
    (∀ N : Matrix (Fin n) (Fin n) K, IsNilpotent N →
      IsNilpotent (truncExp n N - 1) ∧ truncLog n (truncExp n N) = N) ∧
    (∀ u : Matrix (Fin n) (Fin n) K, IsNilpotent (u - 1) →
      IsNilpotent (truncLog n u) ∧ truncExp n (truncLog n u) = u) ∧
    (∀ N : Matrix (Fin n) (Fin n) K, IsNilpotent N → unitaryAdjoint h C N = -N →
      ∃ g : GL (Fin n) K, g ∈ gramSU h (C : Matrix (Fin n) (Fin n) K) ∧
        (g : Matrix (Fin n) (Fin n) K) = truncExp n N ∧
        IsNilpotent ((g : Matrix (Fin n) (Fin n) K) - 1)) ∧
    (∀ g : GL (Fin n) K, g ∈ gramSU h (C : Matrix (Fin n) (Fin n) K) →
      IsNilpotent ((g : Matrix (Fin n) (Fin n) K) - 1) →
      IsNilpotent (truncLog n (g : Matrix (Fin n) (Fin n) K)) ∧
        unitaryAdjoint h C (truncLog n (g : Matrix (Fin n) (Fin n) K)) =
          -truncLog n (g : Matrix (Fin n) (Fin n) K)) ∧
    (∀ (g : GL (Fin n) K) (N : Matrix (Fin n) (Fin n) K),
      truncExp n ((g : Matrix (Fin n) (Fin n) K) * N * (↑(g⁻¹) : Matrix (Fin n) (Fin n) K)) =
        g * truncExp n N * (↑(g⁻¹) : Matrix (Fin n) (Fin n) K)) ∧
    (∀ (g : GL (Fin n) K) (u : Matrix (Fin n) (Fin n) K),
      truncLog n ((g : Matrix (Fin n) (Fin n) K) * u * (↑(g⁻¹) : Matrix (Fin n) (Fin n) K)) =
        g * truncLog n u * (↑(g⁻¹) : Matrix (Fin n) (Fin n) K)) ∧
    (∀ (σ : K ≃+* K) (N : Matrix (Fin n) (Fin n) K),
      truncExp n (N.map σ) = (truncExp n N).map σ) ∧
    (∀ (σ : K ≃+* K) (u : Matrix (Fin n) (Fin n) K),
      truncLog n (u.map σ) = (truncLog n u).map σ) ∧
    (∀ (σ : K ≃+* K) (N : Matrix (Fin n) (Fin n) K),
      unitaryAdjoint h C (N.map σ) = (unitaryAdjoint h C N).map σ) ∧
    (∀ N : Matrix (Fin n) (Fin n) K, IsNilpotent N → ∀ g : GL (Fin n) K,
      Commute (g : Matrix (Fin n) (Fin n) K) (truncExp n N) ↔
        Commute (g : Matrix (Fin n) (Fin n) K) N) ∧
    (∀ u : Matrix (Fin n) (Fin n) K, IsNilpotent (u - 1) → u ^ p = 1) ∧
    (∀ g : GL (Fin n) K, g ∈ gramSU h (C : Matrix (Fin n) (Fin n) K) →
      IsNilpotent ((g : Matrix (Fin n) (Fin n) K) - 1) → g ^ p = 1) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  have hn : 1 ≤ n := by omega
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, -⟩ :=
    small_bilinear_isometry_unipotent_logarithm_calculus (K := K) (p := p) hn hnp
  refine ⟨g1, g2, ?_, ?_, g3, g4, fun σ N => g5 (σ : K →+* K) N, fun σ u => g6 (σ : K →+* K) u,
    fun σ N => KCUnitaryLog.unitaryAdjoint_map h C hC σ N, g7, g8, ?_⟩
  · intro N hN hskew
    have hN' := matrix_pow_eq_zero_of_isNilpotent hN
    exact ⟨KCUnitaryLog.truncExpUnit h hn hnp hN', mem_gramSU.mpr
      ⟨KCUnitaryLog.barTranspose_truncExp_mul h C hn hnp hN' hskew,
        KCUnitaryLog.det_truncExp hn hN'⟩, rfl, (g1 N hN).1⟩
  · intro g hg hu
    exact KCUnitaryLog.unitaryAdjoint_truncLog_of_mem h C hn hnp hg hu
  · intro g _ hu
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, g8 _ hu, Units.val_one])

end CFSG.RankThree.PartOne
