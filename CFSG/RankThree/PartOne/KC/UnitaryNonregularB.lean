module

public import CFSG.RankThree.PartOne.KC.UnitaryNonregularDefs
public import CFSG.RankThree.PartOne.KC.UnitaryDefiningIsotropic
public import CFSG.RankThree.PartOne.KC.UnitaryDefiningRadical

public section

namespace CFSG.RankThree.PartOne

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.GroupTheory

namespace KCUnitaryNr

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem shape_of_comm {X : Matrix (Fin 4) (Fin 4) K} (hX : X * nrNilB K = nrNilB K * X) :
    X 1 0 = 0 ∧ X 2 0 = 0 ∧ X 3 0 = 0 ∧ X 2 1 = 0 ∧ X 3 1 = 0 ∧ X 1 3 = 0 ∧ X 2 3 = 0 ∧
      X 1 1 = X 0 0 ∧ X 2 2 = X 0 0 ∧ X 1 2 = X 0 1 := by
  have e : ∀ i j : Fin 4, (X * nrNilB K) i j = (nrNilB K * X) i j := fun i j => by rw [hX]
  have e00 := e 0 0
  have e01 := e 0 1
  have e02 := e 0 2
  have e03 := e 0 3
  have e10 := e 1 0
  have e11 := e 1 1
  have e12 := e 1 2
  have e13 := e 1 3
  have e21 := e 2 1
  have e22 := e 2 2
  have e31 := e 3 1
  have e32 := e 3 2
  simp [nrNilB, Matrix.mul_apply, Fin.sum_univ_four] at e00 e01 e02 e03
  simp [nrNilB, Matrix.mul_apply, Fin.sum_univ_four] at e10 e11 e12 e13
  simp [nrNilB, Matrix.mul_apply, Fin.sum_univ_four] at e21 e22 e31 e32
  exact ⟨e00.symm, e21, e31, e22, e32, e03.symm, e13.symm, e01.symm, e12.symm.trans e01.symm,
    e02.symm⟩

theorem inv_comm_of_comm {N X Xi : Matrix (Fin 4) (Fin 4) K} (h1 : Xi * X = 1) (h2 : X * Xi = 1)
    (hX : X * N = N * X) : Xi * N = N * Xi := by
  calc Xi * N = Xi * N * (X * Xi) := by rw [h2, Matrix.mul_one]
    _ = Xi * (N * X) * Xi := by simp only [Matrix.mul_assoc]
    _ = Xi * (X * N) * Xi := by rw [hX]
    _ = (Xi * X) * N * Xi := by simp only [Matrix.mul_assoc]
    _ = N * Xi := by rw [h1, Matrix.one_mul]

theorem mul_zero_zero {X Y : Matrix (Fin 4) (Fin 4) K} (hY : Y * nrNilB K = nrNilB K * Y) :
    (X * Y) 0 0 = X 0 0 * Y 0 0 := by
  obtain ⟨y10, y20, y30, -, -, -, -, -, -, -⟩ := shape_of_comm hY
  rw [Matrix.mul_apply, Fin.sum_univ_four, y10, y20, y30]
  ring

theorem mul_three_three {X Y : Matrix (Fin 4) (Fin 4) K} (hX : X * nrNilB K = nrNilB K * X)
    (hY : Y * nrNilB K = nrNilB K * Y) : (X * Y) 3 3 = X 3 3 * Y 3 3 := by
  obtain ⟨-, -, x30, -, x31, -, -, -, -, -⟩ := shape_of_comm hX
  obtain ⟨-, -, -, -, -, -, y23, -, -, -⟩ := shape_of_comm hY
  rw [Matrix.mul_apply, Fin.sum_univ_four, x30, x31, y23]
  ring

@[expose] def IsBUnip (X : Matrix (Fin 4) (Fin 4) K) : Prop :=
  X * nrNilB K = nrNilB K * X ∧ X 0 0 = 1 ∧ X 3 3 = 1

theorem IsBUnip.one : IsBUnip (1 : Matrix (Fin 4) (Fin 4) K) :=
  ⟨by rw [Matrix.one_mul, Matrix.mul_one], Matrix.one_apply_eq _, Matrix.one_apply_eq _⟩

theorem IsBUnip.mul {X Y : Matrix (Fin 4) (Fin 4) K} (hX : IsBUnip X) (hY : IsBUnip Y) :
    IsBUnip (X * Y) := by
  obtain ⟨hX1, hX2, hX3⟩ := hX
  obtain ⟨hY1, hY2, hY3⟩ := hY
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, hY1, ← Matrix.mul_assoc, hX1, Matrix.mul_assoc]
  · rw [mul_zero_zero hY1, hX2, hY2, one_mul]
  · rw [mul_three_three hX1 hY1, hX3, hY3, one_mul]

theorem IsBUnip.of_inv {X Xi : Matrix (Fin 4) (Fin 4) K} (hX : IsBUnip X) (h1 : Xi * X = 1)
    (h2 : X * Xi = 1) : IsBUnip Xi := by
  obtain ⟨hX1, hX2, hX3⟩ := hX
  have hc := inv_comm_of_comm h1 h2 hX1
  refine ⟨hc, ?_, ?_⟩
  · have := congrFun (congrFun h2 0) 0
    rwa [mul_zero_zero hc, hX2, one_mul, Matrix.one_apply_eq] at this
  · have := congrFun (congrFun h2 3) 3
    rwa [mul_three_three hX1 hc, hX3, one_mul, Matrix.one_apply_eq] at this

@[expose] def nrBR : Subgroup (gramSU h (nrGramB K)) where
  carrier := {g | IsBUnip ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)}
  one_mem' := by
    change IsBUnip (((1 : gramSU h (nrGramB K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
    simpa using IsBUnip.one
  mul_mem' := by
    intro a b ha hb
    change IsBUnip (((a * b : gramSU h (nrGramB K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
    simpa only [Subgroup.coe_mul, Units.val_mul] using IsBUnip.mul ha hb
  inv_mem' := by
    intro a ha
    have hai : (((a⁻¹ : gramSU h (nrGramB K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        ((a : GL (Fin 4) K)⁻¹ : GL (Fin 4) K) := rfl
    have h1 : (((a⁻¹ : gramSU h (nrGramB K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        ((a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := by
      rw [hai, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h2 : ((a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        (((a⁻¹ : gramSU h (nrGramB K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := by
      rw [hai, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    exact IsBUnip.of_inv ha h1 h2

theorem mem_nrBR {g : gramSU h (nrGramB K)} :
    g ∈ nrBR h ↔ IsBUnip ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := Iff.rfl

theorem sub_one_pow_three_of_isBUnip {X : Matrix (Fin 4) (Fin 4) K} (hX : IsBUnip X) :
    (X - 1) ^ 3 = 0 := by
  obtain ⟨hc, h00, h33⟩ := hX
  obtain ⟨x10, x20, x30, x21, x31, x13, x23, x11, x22, x12⟩ := shape_of_comm hc
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_four, Matrix.sub_apply, Matrix.one_apply,
      x10, x20, x30, x21, x31, x13, x23, x11, x22, x12, h00, h33]

theorem nrBR_pow_eq_one (hp3 : 3 < p) {g : gramSU h (nrGramB K)} (hg : g ∈ nrBR h) :
    g ^ p = 1 := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  have h3 := sub_one_pow_three_of_isBUnip hg
  set M : Matrix (Fin 4) (Fin 4) K := ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) - 1
    with hM
  have hMp : M ^ p = 0 := by rw [← Nat.sub_add_cancel (by omega : 3 ≤ p), pow_add, h3, mul_zero]
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, Subgroup.coe_one, Units.val_one,
    show ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 + M by rw [hM]; abel,
    add_pow_char_of_commute p (Commute.one_left M), one_pow, hMp, add_zero]

theorem nrBR_conj_mem {g : gramSU h (nrGramB K)}
    (hg : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * nrNilB K =
      nrNilB K * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))
    {r : gramSU h (nrGramB K)} (hr : r ∈ nrBR h) : g * r * g⁻¹ ∈ nrBR h := by
  have hai : (((g⁻¹ : gramSU h (nrGramB K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      ((g : GL (Fin 4) K)⁻¹ : GL (Fin 4) K) := rfl
  have h1 : (((g⁻¹ : gramSU h (nrGramB K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [hai, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      (((g⁻¹ : gramSU h (nrGramB K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [hai, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hgi := inv_comm_of_comm h1 h2 hg
  obtain ⟨hr1, hr2, hr3⟩ := hr
  change IsBUnip (((g * r * g⁻¹ : gramSU h (nrGramB K)) : GL (Fin 4) K) :
    Matrix (Fin 4) (Fin 4) K)
  simp only [Subgroup.coe_mul, Units.val_mul]
  set gm : Matrix (Fin 4) (Fin 4) K := ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
  set gi : Matrix (Fin 4) (Fin 4) K :=
    (((g⁻¹ : gramSU h (nrGramB K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
  set rm : Matrix (Fin 4) (Fin 4) K := ((r : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
  have hgr : gm * rm * nrNilB K = nrNilB K * (gm * rm) := by
    rw [Matrix.mul_assoc, hr1, ← Matrix.mul_assoc, hg, Matrix.mul_assoc]
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc (gm * rm) gi, hgi, ← Matrix.mul_assoc (gm * rm), hgr, Matrix.mul_assoc]
  · rw [mul_zero_zero hgi, mul_zero_zero hr1, hr2, mul_one]
    have := congrFun (congrFun h2 0) 0
    rwa [mul_zero_zero hgi, Matrix.one_apply_eq] at this
  · rw [mul_three_three hgr hgi, mul_three_three hg hr1, hr3, mul_one]
    have := congrFun (congrFun h2 3) 3
    rwa [mul_three_three hg hgi, Matrix.one_apply_eq] at this

@[expose] def nrMd {K : Type} [Field K] (bar : K → K) (d : K) : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, 0, d; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, -bar d, 0]

theorem nrMd_pow_three (d : K) : nrMd h.bar d ^ 3 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nrMd, pow_succ, Matrix.mul_apply, Fin.sum_univ_four]

theorem nrMd_pow_four (d : K) : nrMd h.bar d ^ 4 = 0 := by
  rw [pow_succ, nrMd_pow_three, zero_mul]

theorem nrMd_skew (d : K) : unitaryAdjoint h (nrGLB K) (nrMd h.bar d) = -nrMd h.bar d := by
  rw [unitaryAdjoint_eq_neg_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nrMd, nrGramB, Matrix.mul_apply, Fin.sum_univ_four, h.bar_bar]

theorem truncExp_four_of_pow_three {M : Matrix (Fin 4) (Fin 4) K} (hM : M ^ 3 = 0) :
    truncExp 4 M = 1 + M + (2 : K)⁻¹ • (M * M) := by
  simp only [truncExp, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hM, smul_zero,
    add_zero, Nat.factorial_zero, Nat.factorial_one, Nat.factorial_two, Nat.cast_one, inv_one,
    one_smul, pow_zero, pow_one, pow_two, Nat.cast_ofNat]

include h in
theorem commute_truncExp_of_commute (hp3 : 3 < p) {M Y : Matrix (Fin 4) (Fin 4) K}
    (hM : M ^ 4 = 0) (hY : Y * M = M * Y) : Y * truncExp 4 M = truncExp 4 M * Y :=
  (commute_truncExp_iff (by norm_num) (KCUnitaryLog.hK_of_le h (by omega : 4 ≤ p)) hM Y).mpr hY

theorem coe_nrEltB (hp3 : 3 < p) :
    (((nrEltB h hp3 : gramSU h (nrGramB K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      truncExp 4 (nrNilB K) :=
  rfl

theorem nrEltB_mem (hp3 : 3 < p) : nrEltB h hp3 ∈ nrBR h := by
  rw [mem_nrBR h, coe_nrEltB]
  refine ⟨(commute_truncExp_of_commute h hp3 nrNilB_pow_four rfl).symm, ?_, ?_⟩ <;>
    rw [truncExp_four_of_pow_three nrNilB_pow_three] <;>
    simp [nrNilB]

@[expose] def nrFdMat {K : Type} [Field K] (bar : K → K) (d : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, -(d * bar d) * 2⁻¹, d; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, -bar d, 1]

theorem truncExp_nrMd (d : K) : truncExp 4 (nrMd h.bar d) = nrFdMat h.bar d := by
  rw [truncExp_four_of_pow_three (nrMd_pow_three h d)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nrMd, nrFdMat]
  ring

theorem isBUnip_nrFdMat (d : K) : IsBUnip (nrFdMat h.bar d) := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [nrFdMat, nrNilB, Matrix.mul_apply, Fin.sum_univ_four]
  · simp [nrFdMat]
  · simp [nrFdMat]

@[expose] noncomputable def nrFd (hp3 : 3 < p) (d : K) : gramSU h (nrGramB K) :=
  unitaryExp (C := nrGLB K) h (by norm_num) (by omega) (nrMd_pow_four h d) (nrMd_skew h d)

theorem coe_nrFd (hp3 : 3 < p) (d : K) :
    (((nrFd h hp3 d : gramSU h (nrGramB K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      nrFdMat h.bar d := by
  rw [nrFd, coe_unitaryExp, truncExp_nrMd]

theorem nrFd_mem (hp3 : 3 < p) (d : K) : nrFd h hp3 d ∈ nrBR h := by
  rw [mem_nrBR h, coe_nrFd]
  exact isBUnip_nrFdMat h d

theorem nrNilB_map (σ : K ≃+* K) : (nrNilB K).map σ = nrNilB K := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nrNilB]

theorem gramForm_nrB (x y : Fin 4 → K) :
    gramForm h (nrGramB K) x y =
      h.bar (x 0) * y 2 - h.bar (x 1) * y 1 + h.bar (x 2) * y 0 + h.bar (x 3) * y 3 := by
  simp [gramForm_apply, dotProduct, mulVec, Fin.sum_univ_four, nrGramB]
  ring

theorem mul_map_eq_of_exact {n : ℕ} (A : GL (Fin n) K) (σ : K ≃+* K)
    (E : Matrix (Fin n) (Fin n) K)
    (hE : (A : Matrix (Fin n) (Fin n) K) * E.map σ * (↑(A⁻¹) : Matrix (Fin n) (Fin n) K) = E) :
    (A : Matrix (Fin n) (Fin n) K) * E.map σ = E * (A : Matrix (Fin n) (Fin n) K) := by
  have hAi : (↑(A⁻¹) : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc (A : Matrix (Fin n) (Fin n) K) * E.map σ =
      (A : Matrix (Fin n) (Fin n) K) * E.map σ *
        (↑(A⁻¹) * (A : Matrix (Fin n) (Fin n) K)) := by rw [hAi, Matrix.mul_one]
    _ = ((A : Matrix (Fin n) (Fin n) K) * E.map σ * ↑(A⁻¹)) * (A : Matrix (Fin n) (Fin n) K) :=
        (Matrix.mul_assoc _ _ _).symm
    _ = E * (A : Matrix (Fin n) (Fin n) K) := by rw [hE]

theorem mul_map_eq_of_mem {A : GL (Fin 4) K} {σ : K ≃+* K}
    (hexact : ∀ r ∈ nrBR h, A * glAut σ (r : GL (Fin 4) K) * A⁻¹ = r)
    {r : gramSU h (nrGramB K)} (hr : r ∈ nrBR h) :
    (A : Matrix (Fin 4) (Fin 4) K) * ((r : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map σ =
      ((r : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) := by
  have h1 := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K)) (hexact r hr)
  simp only [Units.val_mul, coe_glAut] at h1
  exact mul_map_eq_of_exact A σ _ h1

theorem nrBR_pointwise (hp3 : 3 < p) (A : primeFormUnitary h (nrGramB K)) (σ : K ≃+* K)
    (hexact : ∀ r ∈ nrBR h,
      (A : GL (Fin 4) K) * glAut σ (r : GL (Fin 4) K) * (A : GL (Fin 4) K)⁻¹ = r) :
    ∃ r' ∈ nrBR h,
      primeFormConjHom h (nrGramB K) A * primeFormFieldHom h (isPrimeFormGram_nrB (K := K)) σ =
        MulAut.conj (r' : primeFormP h (nrGramB K)) := by
  set Am : Matrix (Fin 4) (Fin 4) K := ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hAm
  have hE := mul_map_eq_of_mem h hexact (nrEltB_mem h hp3)
  have hmapN : (truncExp 4 (nrNilB K)).map σ = truncExp 4 (nrNilB K) :=
    calc (truncExp 4 (nrNilB K)).map σ = (truncExp 4 (nrNilB K)).map (σ : K →+* K) := rfl
      _ = truncExp 4 ((nrNilB K).map (σ : K →+* K)) := (truncExp_map _ _).symm
      _ = truncExp 4 (nrNilB K) := congrArg (truncExp 4) (nrNilB_map σ)
  rw [coe_nrEltB, hmapN] at hE
  have hcomm : Am * nrNilB K = nrNilB K * Am :=
    (commute_truncExp_iff (by norm_num) (KCUnitaryLog.hK_of_le h (by omega : 4 ≤ p))
      nrNilB_pow_four Am).mp hE
  obtain ⟨a10, a20, a30, a21, a31, a13, a23, a11, a22, a12⟩ := shape_of_comm hcomm
  have hH : ∀ x y : Fin 4 → K, gramForm h (nrGramB K) (Am *ᵥ x) (Am *ᵥ y) =
      gramForm h (nrGramB K) x y :=
    (gramForm_isometry_iff h _ _).mpr (mem_primeFormUnitary.mp A.2)
  have hn1 : h.bar (Am 0 0) * Am 0 0 = 1 := by
    have h1 := hH (Pi.single 0 1) (Pi.single 2 1)
    rw [gramForm_nrB, gramForm_nrB] at h1
    simp [col_apply, a10, a20, a30, a22] at h1
    linear_combination h1
  have hκ0 : Am 0 0 ≠ 0 := right_ne_zero_of_mul_eq_one hn1
  have hrel : ∀ d : K, Am 0 0 * σ d = d * Am 3 3 := by
    intro d
    have hF : Am * (nrFdMat h.bar d).map σ = nrFdMat h.bar d * Am := by
      have h2 := mul_map_eq_of_mem h hexact (nrFd_mem h hp3 d)
      rwa [coe_nrFd] at h2
    have h1 := congrFun (congrFun hF 0) 3
    simp [Matrix.mul_apply, Fin.sum_univ_four, nrFdMat, a23] at h1
    linear_combination h1
  have h33 : Am 3 3 = Am 0 0 := by
    have h1 := hrel 1
    rw [map_one, mul_one, one_mul] at h1
    exact h1.symm
  have hσ : ∀ t, σ t = t := by
    intro t
    have h1 := hrel t
    rw [h33] at h1
    exact mul_left_cancel₀ hκ0 (by rw [h1, mul_comm])
  have hκn : h.norm (Am 0 0) = 1 := by
    rw [UnitaryFieldData.norm, mul_comm]
    exact hn1
  have hBU : IsBUnip ((Am 0 0)⁻¹ • Am) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [Matrix.smul_mul, Matrix.mul_smul, hcomm]
    · rw [Matrix.smul_apply, smul_eq_mul, inv_mul_cancel₀ hκ0]
    · rw [Matrix.smul_apply, smul_eq_mul, h33, inv_mul_cancel₀ hκ0]
  have hnil : IsNilpotent (Am - Am 0 0 • (1 : Matrix (Fin 4) (Fin 4) K)) := by
    refine ⟨3, ?_⟩
    have e : Am - Am 0 0 • (1 : Matrix (Fin 4) (Fin 4) K) =
        Am 0 0 • ((Am 0 0)⁻¹ • Am - 1) := by
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hκ0, one_smul]
    rw [e, smul_pow, sub_one_pow_three_of_isBUnip hBU, smul_zero]
  obtain ⟨r, hAr, hrm⟩ := exists_gramSU_of_unipotent (C := nrGLB K) h A.2 hκ0 hκn hnil
  refine ⟨r, ?_,
    KCUnitaryDefining.primeFormConjHom_mul_fieldHom_eq_conj h isPrimeFormGram_nrB hAr hσ⟩
  rw [mem_nrBR h, hrm]
  exact hBU

theorem nrB_normalPrimeComplementsTrivial (hp3 : 3 < p) :
    NormalPrimeComplementsTrivial p
      (MulAut.conj (nrEltB h hp3 : primeFormP h (nrGramB K))) := by
  have hn : 3 ≤ 4 := by norm_num
  have hnp : 4 ≤ p := by omega
  refine KCUnitaryDefining.normalPrimeComplementsTrivial_of_radical_data (C := nrGLB K) h hp3 hn
    isPrimeFormGram_nrB (nrEltB h hp3) (unitaryExp_pow_eq_one h hp3 hn hnp isPrimeFormGram_nrB
      nrNilB_pow_four (nrNilB_skew h)) (nrNilB K)
    (fun g hg => (unitaryExp_comm_iff h hp3 hn hnp isPrimeFormGram_nrB nrNilB_pow_four
      (nrNilB_skew h) g).mp hg) (nrBR h)
    (fun r hr => (unitaryExp_comm_iff h hp3 hn hnp isPrimeFormGram_nrB nrNilB_pow_four
      (nrNilB_skew h) r).mpr ((mem_nrBR h).mp hr).1)
    (fun r hr => nrBR_pow_eq_one h hp3 hr)
    (fun g hg r hr => nrBR_conj_mem h hg hr)
    (fun A σ hex => nrBR_pointwise h hp3 A σ hex)

end KCUnitaryNr

end CFSG.RankThree.PartOne
