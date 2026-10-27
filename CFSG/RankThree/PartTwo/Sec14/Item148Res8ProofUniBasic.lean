module

public import CFSG.RankThree.PartTwo.Sec14.Item148Res8ProofLinRat
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData

public section

namespace CFSG.RankThree.PartTwo.Sec14.Item148Res8

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

@[expose] noncomputable def barVec (a : Fin 3 → K) : Fin 3 → K := fun i => h.bar (a i)

theorem barVec_apply (a : Fin 3 → K) (i : Fin 3) : barVec h a i = h.bar (a i) := rfl

theorem barVec_smul (t : K) (a : Fin 3 → K) : barVec h (t • a) = h.bar t • barVec h a := by
  ext i
  simp [barVec_apply, map_mul]

@[expose] noncomputable def suToSL : unitarySU 2 f K 3 →* SpecialLinearGroup (Fin 3) K where
  toFun g := ⟨((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K), ((mem_unitarySU_iff h).mp g.2).1⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem coe_suToSL (g : unitarySU 2 f K 3) :
    ((suToSL h g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
  rfl

theorem suToSL_injective : Function.Injective (suToSL h) := by
  intro g g' hgg
  apply Subtype.ext
  apply Units.ext
  exact congrArg Subtype.val hgg

theorem unitary_of_mem_range {x : SpecialLinearGroup (Fin 3) K} (hx : x ∈ (suToSL h).range) :
    ((x : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * (x : Matrix (Fin 3) (Fin 3) K) = 1 := by
  obtain ⟨g, rfl⟩ := hx
  exact ((mem_unitarySU_iff h).mp g.2).2

theorem inv_eq_of_mem_range {x : SpecialLinearGroup (Fin 3) K} (hx : x ∈ (suToSL h).range) :
    ((x⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((x : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ := by
  have hu := unitary_of_mem_range h hx
  have hxi : ((x⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      (x : Matrix (Fin 3) (Fin 3) K) = 1 := by
    have : ((x⁻¹ * x : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
      rw [inv_mul_cancel]; rfl
    exact this
  have hix : (x : Matrix (Fin 3) (Fin 3) K) *
      ((x⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    have : ((x * x⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
      rw [mul_inv_cancel]; rfl
    exact this
  calc ((x⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        (((x : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * (x : Matrix (Fin 3) (Fin 3) K)) *
          ((x⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
        rw [hu, Matrix.one_mul]
    _ = ((x : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ := by
        rw [Matrix.mul_assoc, hix, Matrix.mul_one]

theorem barVec_vecMul_inv {x : SpecialLinearGroup (Fin 3) K} (hx : x ∈ (suToSL h).range)
    (a : Fin 3 → K) :
    barVec h a ᵥ* ((x⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      barVec h ((x : Matrix (Fin 3) (Fin 3) K) *ᵥ a) := by
  rw [inv_eq_of_mem_range h hx]
  ext j
  simp [Matrix.vecMul, Matrix.mulVec, dotProduct, barVec_apply, map_sum, map_mul,
    Matrix.transpose_apply, Matrix.map_apply, mul_comm]

theorem tvMat_unitary (a : Fin 3 → K) (ha : barVec h a ⬝ᵥ a = 0) {c : K} (hc : h.bar c = c) :
    ((1 + c • vecMulVec a (barVec h a)).map h.bar)ᵀ * (1 + c • vecMulVec a (barVec h a)) = 1 := by
  have : CharP K 2 := h.charP
  have e : ((1 + c • vecMulVec a (barVec h a)).map h.bar)ᵀ = 1 + c • vecMulVec a (barVec h a) := by
    ext i j
    simp [Matrix.map_apply, Matrix.transpose_apply, vecMulVec_apply, barVec_apply,
      Matrix.one_apply, map_add, map_mul, hc, UnitaryFieldData.bar_bar, mul_comm, eq_comm]
  set N := vecMulVec a (barVec h a) with hN
  have hN2 : N * N = 0 := by
    rw [hN, vecMulVec_mul_vecMulVec, ha, zero_smul]
    ext i j
    simp [vecMulVec_apply]
  rw [e]
  calc (1 + c • N) * (1 + c • N) = 1 + (c + c) • N + (c * c) • (N * N) := by
        simp only [add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
          Matrix.mul_smul, smul_smul, add_smul]
        abel
    _ = 1 := by rw [hN2, smul_zero, add_zero, CharTwo.add_self_eq_zero, zero_smul, add_zero]

@[expose] noncomputable def tvSU (a : Fin 3 → K) (ha : barVec h a ⬝ᵥ a = 0) {c : K}
    (hc : h.bar c = c) : unitarySU 2 f K 3 :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (1 + c • vecMulVec a (barVec h a))
      (by rw [det_one_add_smul_vecMulVec, ha, mul_zero, add_zero]; exact one_ne_zero),
    (mem_unitarySU_iff h).mpr ⟨by
      show (1 + c • vecMulVec a (barVec h a)).det = 1
      rw [det_one_add_smul_vecMulVec, ha, mul_zero, add_zero],
      tvMat_unitary h a ha hc⟩⟩

theorem suToSL_tvSU (a : Fin 3 → K) (ha : barVec h a ⬝ᵥ a = 0) {c : K} (hc : h.bar c = c) :
    suToSL h (tvSU h a ha hc) = rankOneSL a (barVec h a) ha c :=
  rfl

theorem bar_eq_of_rankOneSL_mem {a : Fin 3 → K} (ha : barVec h a ⬝ᵥ a = 0) (ha0 : a ≠ 0)
    {c : K} (hc : rankOneSL a (barVec h a) ha c ∈ (suToSL h).range) : h.bar c = c := by
  have : CharP K 2 := h.charP
  have hu := unitary_of_mem_range h hc
  rw [coe_rankOneSL] at hu
  have e : ((1 + c • vecMulVec a (barVec h a)).map h.bar)ᵀ =
      1 + h.bar c • vecMulVec a (barVec h a) := by
    ext i j
    simp [Matrix.map_apply, Matrix.transpose_apply, vecMulVec_apply, barVec_apply,
      Matrix.one_apply, map_add, map_mul, UnitaryFieldData.bar_bar, mul_comm, eq_comm]
  set N₀ := vecMulVec a (barVec h a) with hN₀
  have hN2 : N₀ * N₀ = 0 := by
    rw [hN₀, vecMulVec_mul_vecMulVec, ha, zero_smul]
    ext i j
    simp [vecMulVec_apply]
  rw [e] at hu
  have hexp : (1 + h.bar c • N₀) * (1 + c • N₀) = 1 + (h.bar c + c) • N₀ := by
    simp only [add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, add_smul, hN2, smul_zero, add_zero]
    abel
  rw [hexp] at hu
  have hN : (h.bar c + c) • N₀ = 0 := by
    have := congrArg (· - 1) hu
    simpa using this
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra hall
    push Not at hall
    exact ha0 (funext hall)
  have hii : (h.bar c + c) * (a i * h.bar (a i)) = 0 := by
    have := congrFun (congrFun hN i) i
    rw [hN₀] at this
    simpa [vecMulVec_apply, barVec_apply] using this
  have hbi : h.bar (a i) ≠ 0 := by
    intro h0
    apply hi
    have := congrArg h.bar h0
    rwa [UnitaryFieldData.bar_bar, map_zero] at this
  have hsum : h.bar c + c = 0 := by
    rcases mul_eq_zero.mp hii with h1 | h1
    · exact h1
    · exact absurd h1 (mul_ne_zero hi hbi)
  have h2 : c + c = 0 := CharTwo.add_self_eq_zero c
  linear_combination hsum - h2

theorem conj_rankOneSL_bar {x : SpecialLinearGroup (Fin 3) K} (hx : x ∈ (suToSL h).range)
    {a : Fin 3 → K} (ha : barVec h a ⬝ᵥ a = 0)
    (hxa : barVec h ((x : Matrix (Fin 3) (Fin 3) K) *ᵥ a) ⬝ᵥ
      ((x : Matrix (Fin 3) (Fin 3) K) *ᵥ a) = 0) (c : K) :
    x * rankOneSL a (barVec h a) ha c * x⁻¹ =
      rankOneSL ((x : Matrix (Fin 3) (Fin 3) K) *ᵥ a)
        (barVec h ((x : Matrix (Fin 3) (Fin 3) K) *ᵥ a)) hxa c := by
  apply Subtype.ext
  show (x : Matrix (Fin 3) (Fin 3) K) * (1 + c • vecMulVec a (barVec h a)) *
      ((x⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
    1 + c • vecMulVec ((x : Matrix (Fin 3) (Fin 3) K) *ᵥ a)
      (barVec h ((x : Matrix (Fin 3) (Fin 3) K) *ᵥ a))
  have hix : (x : Matrix (Fin 3) (Fin 3) K) *
      ((x⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    have : ((x * x⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
      rw [mul_inv_cancel]; rfl
    exact this
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hix, Matrix.mul_smul, Matrix.smul_mul,
    mul_vecMulVec, vecMulVec_mul, barVec_vecMul_inv h hx]

end CFSG.RankThree.PartTwo.Sec14.Item148Res8
