module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartOne.KC.UnitaryLogCalculus

public section

namespace CFSG.RankThree.PartOne

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

@[expose] def nrGramA (K : Type) [Field K] : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]

@[expose] def nrNilA {K : Type} [Field K] (η : K) : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, η, 0; 0, 0, 0, η; 0, 0, 0, 0; 0, 0, 0, 0]

@[expose] def nrGramB (K : Type) [Field K] : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, 1, 0; 0, -1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1]

@[expose] def nrNilB (K : Type) [Field K] : Matrix (Fin 4) (Fin 4) K :=
  !![0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0; 0, 0, 0, 0]

namespace KCUnitaryNr

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem nrGramA_mul_self : nrGramA K * nrGramA K = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nrGramA, Matrix.mul_apply, Fin.sum_univ_four]

theorem nrGramB_mul_self : nrGramB K * nrGramB K = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nrGramB, Matrix.mul_apply, Fin.sum_univ_four]

abbrev nrGLA (K : Type) [Field K] : GL (Fin 4) K :=
  ⟨nrGramA K, nrGramA K, nrGramA_mul_self, nrGramA_mul_self⟩

abbrev nrGLB (K : Type) [Field K] : GL (Fin 4) K :=
  ⟨nrGramB K, nrGramB K, nrGramB_mul_self, nrGramB_mul_self⟩

theorem isPrimeFormGram_nrA : IsPrimeFormGram (nrGLA K) := by
  refine ⟨?_, fun i j => ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [nrGramA]
  · fin_cases i <;> fin_cases j <;>
      simp [nrGramA, zero_mem, one_mem]

theorem isPrimeFormGram_nrB : IsPrimeFormGram (nrGLB K) := by
  refine ⟨?_, fun i j => ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [nrGramB]
  · fin_cases i <;> fin_cases j <;>
      simp [nrGramB, zero_mem, one_mem]

theorem unitaryAdjoint_eq_neg_iff {n : ℕ} (C : GL (Fin n) K) (N : Matrix (Fin n) (Fin n) K) :
    unitaryAdjoint h C N = -N ↔ (N.map h.bar)ᵀ * (C : Matrix (Fin n) (Fin n) K) =
      -((C : Matrix (Fin n) (Fin n) K) * N) := by
  have hC : (C : Matrix (Fin n) (Fin n) K) * (↑(C⁻¹) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hC' : (↑(C⁻¹) : Matrix (Fin n) (Fin n) K) * (C : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  unfold unitaryAdjoint
  constructor
  · intro hN
    calc (N.map h.bar)ᵀ * (C : Matrix (Fin n) (Fin n) K)
        = (C : Matrix (Fin n) (Fin n) K) * ((↑(C⁻¹) : Matrix (Fin n) (Fin n) K) *
            (N.map h.bar)ᵀ * (C : Matrix (Fin n) (Fin n) K)) := by
          simp only [← Matrix.mul_assoc, hC, Matrix.one_mul]
      _ = -((C : Matrix (Fin n) (Fin n) K) * N) := by rw [hN, Matrix.mul_neg]
  · intro hN
    calc (↑(C⁻¹) : Matrix (Fin n) (Fin n) K) * (N.map h.bar)ᵀ * (C : Matrix (Fin n) (Fin n) K)
        = (↑(C⁻¹) : Matrix (Fin n) (Fin n) K) * ((N.map h.bar)ᵀ *
            (C : Matrix (Fin n) (Fin n) K)) := by rw [Matrix.mul_assoc]
      _ = -N := by rw [hN, Matrix.mul_neg, ← Matrix.mul_assoc, hC', Matrix.one_mul]

theorem nrNilA_skew {η : K} (hη : h.bar η = -η) :
    unitaryAdjoint h (nrGLA K) (nrNilA η) = -nrNilA η := by
  rw [unitaryAdjoint_eq_neg_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nrNilA, nrGramA, Matrix.mul_apply, Fin.sum_univ_four, hη]

theorem nrNilB_skew : unitaryAdjoint h (nrGLB K) (nrNilB K) = -nrNilB K := by
  rw [unitaryAdjoint_eq_neg_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nrNilB, nrGramB, Matrix.mul_apply, Fin.sum_univ_four]

theorem nrNilA_sq (η : K) : nrNilA η * nrNilA η = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nrNilA, Matrix.mul_apply, Fin.sum_univ_four]

theorem nrNilA_pow_four (η : K) : nrNilA η ^ 4 = 0 := by
  have h2 : nrNilA η ^ 2 = 0 := by rw [pow_two, nrNilA_sq]
  calc nrNilA η ^ 4 = nrNilA η ^ 2 * nrNilA η ^ 2 := by rw [← pow_add]
    _ = 0 := by rw [h2, zero_mul]

theorem nrNilB_pow_three : nrNilB K ^ 3 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nrNilB, pow_succ, Matrix.mul_apply, Fin.sum_univ_four]

theorem nrNilB_pow_four : nrNilB K ^ 4 = 0 := by
  rw [pow_succ, nrNilB_pow_three, zero_mul]

theorem smul_inv_mem_primeFormUnitary {n : ℕ} {C : GL (Fin n) K}
    {A : GL (Fin n) K} (hA : A ∈ primeFormUnitary h (C : Matrix (Fin n) (Fin n) K)) {κ : K}
    (hκn : h.norm κ = 1) :
    (((κ⁻¹ • (A : Matrix (Fin n) (Fin n) K)).map h.bar)ᵀ * (C : Matrix (Fin n) (Fin n) K) *
      (κ⁻¹ • (A : Matrix (Fin n) (Fin n) K))) = (C : Matrix (Fin n) (Fin n) K) := by
  have hA' : ((A : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (C : Matrix (Fin n) (Fin n) K) *
      (A : Matrix (Fin n) (Fin n) K) = C := hA
  rw [Matrix.map_smul' _ _ _ (map_mul h.bar), Matrix.transpose_smul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [hA', map_inv₀]
  have : κ⁻¹ * (h.bar κ)⁻¹ = 1 := by
    rw [← mul_inv, show κ * h.bar κ = 1 from hκn, inv_one]
  rw [this, one_smul]

theorem exists_gramSU_of_unipotent {n : ℕ} {C : GL (Fin n) K} {A : GL (Fin n) K}
    (hA : A ∈ primeFormUnitary h (C : Matrix (Fin n) (Fin n) K)) {κ : K} (hκ : κ ≠ 0)
    (hκn : h.norm κ = 1)
    (hnil : IsNilpotent ((A : Matrix (Fin n) (Fin n) K) - κ • (1 : Matrix (Fin n) (Fin n) K))) :
    ∃ r : gramSU h (C : Matrix (Fin n) (Fin n) K),
      (A : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) (Units.mk0 κ hκ) *
        (r : GL (Fin n) K) ∧
      ((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = κ⁻¹ • (A : Matrix (Fin n) (Fin n) K) := by
  set u₀ : GL (Fin n) K := GeneralLinearGroup.scalar (Fin n) (Units.mk0 κ hκ)⁻¹ * A with hu₀
  have hu₀m : ((u₀ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      κ⁻¹ • (A : Matrix (Fin n) (Fin n) K) := by
    rw [hu₀, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_eq_diagonal_mul]
    rfl
  have hdet : ((u₀ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 := by
    have h1 : ((u₀ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        1 + κ⁻¹ • ((A : Matrix (Fin n) (Fin n) K) - κ • (1 : Matrix (Fin n) (Fin n) K)) := by
      rw [hu₀m, smul_sub, smul_smul, inv_mul_cancel₀ hκ, one_smul]
      abel
    have h2 : IsNilpotent (κ⁻¹ • ((A : Matrix (Fin n) (Fin n) K) -
        κ • (1 : Matrix (Fin n) (Fin n) K))) := by
      obtain ⟨k, hk⟩ := hnil
      exact ⟨k, by rw [smul_pow, hk, smul_zero]⟩
    rw [h1]
    exact KCUnitaryLog.det_one_add_of_isNilpotent h2
  have hmem : u₀ ∈ gramSU h (C : Matrix (Fin n) (Fin n) K) :=
    mem_gramSU.mpr ⟨by rw [hu₀m]; exact smul_inv_mem_primeFormUnitary h hA hκn, hdet⟩
  refine ⟨⟨u₀, hmem⟩, ?_, hu₀m⟩
  change A = GeneralLinearGroup.scalar (Fin n) (Units.mk0 κ hκ) * u₀
  rw [hu₀, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]


theorem unitaryExp_pow_eq_one {n : ℕ} (hp3 : 3 < p) (hn : 3 ≤ n) (hnp : n ≤ p)
    {C : GL (Fin n) K} (hC : IsPrimeFormGram C) {N : Matrix (Fin n) (Fin n) K} (hN : N ^ n = 0)
    (hskew : unitaryAdjoint h C N = -N) : unitaryExp h hn hnp hN hskew ^ p = 1 := by
  obtain ⟨c1, -, -, -, -, -, -, -, -, -, -, c12⟩ :=
    unitary_small_unipotent_logarithm_calculus h hp3 hn hnp hC
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  exact c12 _ (unitaryExp h hn hnp hN hskew).2 (by
    rw [coe_unitaryExp]
    exact (c1 N ⟨n, hN⟩).1)

theorem unitaryExp_comm_iff {n : ℕ} (hp3 : 3 < p) (hn : 3 ≤ n) (hnp : n ≤ p)
    {C : GL (Fin n) K} (hC : IsPrimeFormGram C) {N : Matrix (Fin n) (Fin n) K} (hN : N ^ n = 0)
    (hskew : unitaryAdjoint h C N = -N) (g : gramSU h (C : Matrix (Fin n) (Fin n) K)) :
    g * unitaryExp h hn hnp hN hskew = unitaryExp h hn hnp hN hskew * g ↔
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * N =
        N * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, c7, -, -⟩ :=
    unitary_small_unipotent_logarithm_calculus h hp3 hn hnp hC
  have h1 := c7 N ⟨n, hN⟩ (g : GL (Fin n) K)
  rw [← coe_unitaryExp h hn hnp hN hskew] at h1
  constructor
  · intro hg
    have h2 := congrArg (fun z : gramSU h (C : Matrix (Fin n) (Fin n) K) =>
      ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) hg
    simp only [Subgroup.coe_mul, Units.val_mul] at h2
    exact h1.mp h2
  · intro hg
    have h2 := h1.mpr hg
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul]
    exact h2


end KCUnitaryNr

@[expose] noncomputable def nrEltA {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hp3 : 3 < p) {η : K} (hη : h.bar η = -η) : gramSU h (nrGramA K) :=
  unitaryExp (C := KCUnitaryNr.nrGLA K) h (by norm_num) (by omega) (KCUnitaryNr.nrNilA_pow_four η)
    (KCUnitaryNr.nrNilA_skew h hη)

@[expose] noncomputable def nrEltB {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hp3 : 3 < p) : gramSU h (nrGramB K) :=
  unitaryExp (C := KCUnitaryNr.nrGLB K) h (by norm_num) (by omega) (KCUnitaryNr.nrNilB_pow_four)
    (KCUnitaryNr.nrNilB_skew h)

end CFSG.RankThree.PartOne
