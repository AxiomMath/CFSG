module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVQuasi

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429.RowV

open Matrix
open scoped commutatorElement

theorem mem_centralizer_diagonal_iff {n : ℕ} {K : Type*} [Field K] {x : Fin n → K}
    {d h : Matrix.SpecialLinearGroup (Fin n) K}
    (hd : (d : Matrix (Fin n) (Fin n) K) = Matrix.diagonal x) :
    h ∈ Subgroup.centralizer ({d} : Set (Matrix.SpecialLinearGroup (Fin n) K)) ↔
      ∀ a b, x a ≠ x b → (h : Matrix (Fin n) (Fin n) K) a b = 0 := by
  have key : h * d = d * h ↔
      (h : Matrix (Fin n) (Fin n) K) * Matrix.diagonal x =
        Matrix.diagonal x * (h : Matrix (Fin n) (Fin n) K) := by
    rw [← hd]
    constructor
    · intro e
      simpa only [Matrix.SpecialLinearGroup.coe_mul] using
        congrArg (fun A : Matrix.SpecialLinearGroup (Fin n) K => (A : Matrix (Fin n) (Fin n) K)) e
    · intro e
      apply Subtype.ext
      simpa only [Matrix.SpecialLinearGroup.coe_mul] using e
  rw [Subgroup.mem_centralizer_singleton_iff, key]
  constructor
  · intro hc a b hab
    have hentry : ((h : Matrix (Fin n) (Fin n) K) * Matrix.diagonal x) a b =
        (Matrix.diagonal x * (h : Matrix (Fin n) (Fin n) K)) a b := by
      rw [hc]
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at hentry
    have hm : (x a - x b) * (h : Matrix (Fin n) (Fin n) K) a b = 0 := by
      linear_combination -hentry
    rcases mul_eq_zero.mp hm with h0 | h0
    · exact absurd (sub_eq_zero.mp h0) hab
    · exact h0
  · intro hz
    ext a b
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hab : x a = x b
    · rw [hab, mul_comm]
    · rw [hz a b hab, zero_mul, mul_zero]

private def blk_mat {K : Type*} [Field K] (i : Fin 4) (B : Matrix (Fin 3) (Fin 3) K) :
    Matrix (Fin 4) (Fin 4) K :=
  Matrix.of fun a => Fin.insertNth (α := fun _ => Fin 4 → K) i
    (fun j => if j = i then 1 else 0) (fun k => Fin.insertNth (α := fun _ => K) i 0 (B k)) a

private theorem blk_mat_self_row {K : Type*} [Field K] (i : Fin 4)
    (B : Matrix (Fin 3) (Fin 3) K) (j : Fin 4) :
    blk_mat i B i j = if j = i then 1 else 0 := by
  simp only [blk_mat, Matrix.of_apply, Fin.insertNth_apply_same]

private theorem blk_mat_self_self {K : Type*} [Field K] (i : Fin 4)
    (B : Matrix (Fin 3) (Fin 3) K) : blk_mat i B i i = 1 := by
  rw [blk_mat_self_row]
  simp

private theorem blk_mat_self_succ {K : Type*} [Field K] (i : Fin 4)
    (B : Matrix (Fin 3) (Fin 3) K) (l : Fin 3) : blk_mat i B i (i.succAbove l) = 0 := by
  rw [blk_mat_self_row, if_neg (Fin.succAbove_ne i l)]

private theorem blk_mat_succ_self {K : Type*} [Field K] (i : Fin 4)
    (B : Matrix (Fin 3) (Fin 3) K) (k : Fin 3) : blk_mat i B (i.succAbove k) i = 0 := by
  simp only [blk_mat, Matrix.of_apply, Fin.insertNth_apply_succAbove, Fin.insertNth_apply_same]

private theorem blk_mat_succ_succ {K : Type*} [Field K] (i : Fin 4)
    (B : Matrix (Fin 3) (Fin 3) K) (k l : Fin 3) :
    blk_mat i B (i.succAbove k) (i.succAbove l) = B k l := by
  simp only [blk_mat, Matrix.of_apply, Fin.insertNth_apply_succAbove]

private theorem blk_ext {K : Type*} (i : Fin 4) {M N : Matrix (Fin 4) (Fin 4) K}
    (h1 : M i i = N i i) (h2 : ∀ l : Fin 3, M i (i.succAbove l) = N i (i.succAbove l))
    (h3 : ∀ k : Fin 3, M (i.succAbove k) i = N (i.succAbove k) i)
    (h4 : ∀ k l : Fin 3, M (i.succAbove k) (i.succAbove l) = N (i.succAbove k) (i.succAbove l)) :
    M = N := by
  ext a b
  by_cases ha : a = i
  · rw [ha]
    by_cases hb : b = i
    · rw [hb]
      exact h1
    · obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hb
      exact h2 l
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq ha
    by_cases hb : b = i
    · rw [hb]
      exact h3 k
    · obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hb
      exact h4 k l

private theorem blk_mat_injective {K : Type*} [Field K] (i : Fin 4) :
    Function.Injective (blk_mat (K := K) i) := by
  intro B C h
  ext k l
  have h' : blk_mat i B (i.succAbove k) (i.succAbove l) =
      blk_mat i C (i.succAbove k) (i.succAbove l) := by
    rw [h]
  rwa [blk_mat_succ_succ, blk_mat_succ_succ] at h'

private theorem blk_mat_one {K : Type*} [Field K] (i : Fin 4) :
    blk_mat i (1 : Matrix (Fin 3) (Fin 3) K) = 1 := by
  refine blk_ext i ?_ ?_ ?_ ?_
  · rw [blk_mat_self_self, Matrix.one_apply_eq]
  · intro l
    rw [blk_mat_self_succ, Matrix.one_apply_ne (Fin.succAbove_ne i l).symm]
  · intro k
    rw [blk_mat_succ_self, Matrix.one_apply_ne (Fin.succAbove_ne i k)]
  · intro k l
    simp only [blk_mat_succ_succ, Matrix.one_apply, Fin.succAbove_right_inj]

private theorem blk_mat_mul {K : Type*} [Field K] (i : Fin 4) (B C : Matrix (Fin 3) (Fin 3) K) :
    blk_mat i B * blk_mat i C = blk_mat i (B * C) := by
  refine blk_ext i ?_ ?_ ?_ ?_
  · simp [Matrix.mul_apply, Fin.sum_univ_succAbove _ i, blk_mat_self_self, blk_mat_self_succ,
      blk_mat_succ_self, blk_mat_succ_succ]
  · intro l
    simp [Matrix.mul_apply, Fin.sum_univ_succAbove _ i, blk_mat_self_self, blk_mat_self_succ,
      blk_mat_succ_self, blk_mat_succ_succ]
  · intro k
    simp [Matrix.mul_apply, Fin.sum_univ_succAbove _ i, blk_mat_self_self, blk_mat_self_succ,
      blk_mat_succ_self, blk_mat_succ_succ]
  · intro k l
    simp [Matrix.mul_apply, Fin.sum_univ_succAbove _ i, blk_mat_self_self, blk_mat_self_succ,
      blk_mat_succ_self, blk_mat_succ_succ]

private theorem blk_mat_det {K : Type*} [Field K] (i : Fin 4) (B : Matrix (Fin 3) (Fin 3) K) :
    (blk_mat i B).det = B.det := by
  have hsub : (blk_mat i B).submatrix i.succAbove i.succAbove = B := by
    ext k l
    exact blk_mat_succ_succ i B k l
  rw [Matrix.det_succ_row (blk_mat i B) i, Finset.sum_eq_single i]
  · have hs : (-1 : K) ^ ((i : ℕ) + (i : ℕ)) = 1 := by
      rw [← two_mul, pow_mul, neg_one_sq, one_pow]
    rw [blk_mat_self_self, hsub, hs]
    ring
  · intro j _ hj
    rw [blk_mat_self_row, if_neg hj, mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

private def blk_sl {K : Type*} [Field K] (i : Fin 4) :
    Matrix.SpecialLinearGroup (Fin 3) K →* Matrix.SpecialLinearGroup (Fin 4) K where
  toFun B := ⟨blk_mat i (B : Matrix (Fin 3) (Fin 3) K), by
    rw [blk_mat_det]
    exact Matrix.SpecialLinearGroup.det_coe B⟩
  map_one' := by
    apply Subtype.ext
    show blk_mat i ((1 : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((1 : Matrix.SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
    rw [Matrix.SpecialLinearGroup.coe_one, Matrix.SpecialLinearGroup.coe_one, blk_mat_one]
  map_mul' B C := by
    apply Subtype.ext
    show blk_mat i ((B * C : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      blk_mat i (B : Matrix (Fin 3) (Fin 3) K) * blk_mat i (C : Matrix (Fin 3) (Fin 3) K)
    rw [Matrix.SpecialLinearGroup.coe_mul, blk_mat_mul]

private theorem blk_sl_injective {K : Type*} [Field K] (i : Fin 4) :
    Function.Injective (blk_sl (K := K) i) := by
  intro B C h
  apply Subtype.ext
  apply blk_mat_injective i
  exact congrArg Subtype.val h

private abbrev blk_H {K : Type*} [Field K] (i : Fin 4) :
    Subgroup (Matrix.SpecialLinearGroup (Fin 4) K) :=
  (blk_sl i).range

private theorem blk_mem_range {K : Type*} [Field K] (i : Fin 4)
    (g : Matrix.SpecialLinearGroup (Fin 4) K)
    (hrow : ∀ j, j ≠ i → (g : Matrix (Fin 4) (Fin 4) K) i j = 0)
    (hcol : ∀ j, j ≠ i → (g : Matrix (Fin 4) (Fin 4) K) j i = 0)
    (hii : (g : Matrix (Fin 4) (Fin 4) K) i i = 1) : g ∈ blk_H i := by
  have hEq : (g : Matrix (Fin 4) (Fin 4) K) =
      blk_mat i ((g : Matrix (Fin 4) (Fin 4) K).submatrix i.succAbove i.succAbove) := by
    refine blk_ext i ?_ ?_ ?_ ?_
    · rw [blk_mat_self_self, hii]
    · intro l
      rw [blk_mat_self_succ]
      exact hrow _ (Fin.succAbove_ne i l)
    · intro k
      rw [blk_mat_succ_self]
      exact hcol _ (Fin.succAbove_ne i k)
    · intro k l
      simp only [blk_mat_succ_succ, Matrix.submatrix_apply]
  have hdet : ((g : Matrix (Fin 4) (Fin 4) K).submatrix i.succAbove i.succAbove).det = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe g
    rw [hEq, blk_mat_det] at h
    exact h
  refine MonoidHom.mem_range.mpr ⟨⟨_, hdet⟩, ?_⟩
  apply Subtype.ext
  exact hEq.symm

theorem centQuasi_diagonal_block {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    {c : K} (hc1 : c ≠ 1) (hc3 : c ^ 3 = 1) (i : Fin 4)
    (d : Matrix.SpecialLinearGroup (Fin 4) K)
    (hd : (d : Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal (fun j => if j = i then 1 else c))
    (N₁ : ℕ) : CentQuasi d N₁ 60480 := by
  have hdet : (c • (1 : Matrix (Fin 3) (Fin 3) K)).det = 1 := by
    rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one, hc3]
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : Matrix.SpecialLinearGroup (Fin 3) K,
      (C₀ : Matrix (Fin 3) (Fin 3) K) = c • 1 :=
    ⟨⟨c • 1, hdet⟩, rfl⟩
  have hdC : d = blk_sl i C₀ := by
    apply Subtype.ext
    show (d : Matrix (Fin 4) (Fin 4) K) = blk_mat i (C₀ : Matrix (Fin 3) (Fin 3) K)
    rw [hC₀, hd]
    refine blk_ext i ?_ ?_ ?_ ?_
    · simp [blk_mat_self_self]
    · intro l
      rw [blk_mat_self_succ, Matrix.diagonal_apply_ne _ (Fin.succAbove_ne i l).symm]
    · intro k
      rw [blk_mat_succ_self, Matrix.diagonal_apply_ne _ (Fin.succAbove_ne i k)]
    · intro k l
      rw [blk_mat_succ_succ]
      by_cases hkl : k = l
      · simp [hkl, Fin.succAbove_ne]
      · simp [hkl, Fin.succAbove_right_inj, Matrix.diagonal_apply_ne, Matrix.one_apply]
  have hBC : ∀ B : Matrix.SpecialLinearGroup (Fin 3) K, B * C₀ = C₀ * B := by
    intro B
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hC₀,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
  have hHC : blk_H i ≤ Subgroup.centralizer ({d} : Set (Matrix.SpecialLinearGroup (Fin 4) K)) := by
    rintro _ ⟨B, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hdC, ← map_mul, ← map_mul, hBC B]
  have hdH : d ∈ blk_H i := MonoidHom.mem_range.mpr ⟨C₀, hdC.symm⟩
  have hdcen : ∀ h ∈ blk_H i, h * d = d * h := fun h hh =>
    Subgroup.mem_centralizer_singleton_iff.mp (hHC hh)
  have hd1 : d ≠ 1 := by
    obtain ⟨j, hj⟩ := exists_ne i
    intro h
    have h' := congrArg
      (fun A : Matrix.SpecialLinearGroup (Fin 4) K => (A : Matrix (Fin 4) (Fin 4) K) j j) h
    simp [hd, hj] at h'
    exact hc1 h'
  have hC₀3 : C₀ ^ 3 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hC₀, smul_pow, one_pow, hc3, one_smul,
      Matrix.SpecialLinearGroup.coe_one]
  have hd3 : d ^ 3 = 1 := by
    rw [hdC, ← map_pow, hC₀3, map_one]
  have hvan : ∀ g ∈ Subgroup.centralizer ({d} : Set (Matrix.SpecialLinearGroup (Fin 4) K)),
      (∀ j, j ≠ i → (g : Matrix (Fin 4) (Fin 4) K) i j = 0) ∧
        (∀ j, j ≠ i → (g : Matrix (Fin 4) (Fin 4) K) j i = 0) := by
    intro g hg
    rw [mem_centralizer_diagonal_iff hd] at hg
    exact ⟨fun j hj => hg i j (by simp [hj, Ne.symm hc1]),
      fun j hj => hg j i (by simp [hj, hc1])⟩
  have hχ : ∀ g h : Matrix.SpecialLinearGroup (Fin 4) K,
      (∀ j, j ≠ i → (g : Matrix (Fin 4) (Fin 4) K) i j = 0) →
        ((g * h : Matrix.SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i i =
          (g : Matrix (Fin 4) (Fin 4) K) i i * (h : Matrix (Fin 4) (Fin 4) K) i i := by
    intro g h hrow
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Finset.sum_eq_single i]
    · intro j _ hj
      rw [hrow j hj, zero_mul]
    · intro h'
      exact absurd (Finset.mem_univ i) h'
  have hcomm : ∀ a ∈ Subgroup.centralizer ({d} : Set (Matrix.SpecialLinearGroup (Fin 4) K)),
      ∀ b ∈ Subgroup.centralizer ({d} : Set (Matrix.SpecialLinearGroup (Fin 4) K)),
        ⁅a, b⁆ ∈ blk_H i := by
    intro a ha b hb
    have hab : a * b ∈ Subgroup.centralizer ({d} : Set (Matrix.SpecialLinearGroup (Fin 4) K)) :=
      mul_mem ha hb
    have habi : a * b * a⁻¹ ∈
        Subgroup.centralizer ({d} : Set (Matrix.SpecialLinearGroup (Fin 4) K)) :=
      mul_mem hab (inv_mem ha)
    have hcommC : ⁅a, b⁆ ∈
        Subgroup.centralizer ({d} : Set (Matrix.SpecialLinearGroup (Fin 4) K)) := by
      rw [commutatorElement_def]
      exact mul_mem habi (inv_mem hb)
    have h1 : (a : Matrix (Fin 4) (Fin 4) K) i i *
        ((a⁻¹ : Matrix.SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i i = 1 := by
      rw [← hχ _ _ (hvan _ ha).1, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one,
        Matrix.one_apply_eq]
    have h2 : (b : Matrix (Fin 4) (Fin 4) K) i i *
        ((b⁻¹ : Matrix.SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i i = 1 := by
      rw [← hχ _ _ (hvan _ hb).1, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one,
        Matrix.one_apply_eq]
    have hii : ((⁅a, b⁆ : Matrix.SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i i
        = 1 := by
      rw [commutatorElement_def, hχ _ _ (hvan _ habi).1, hχ _ _ (hvan _ hab).1,
        hχ _ _ (hvan _ ha).1]
      have key : ((a : Matrix (Fin 4) (Fin 4) K) i i *
          ((a⁻¹ : Matrix.SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i i) *
          ((b : Matrix (Fin 4) (Fin 4) K) i i *
          ((b⁻¹ : Matrix.SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i i) = 1 := by
        rw [h1, h2, mul_one]
      linear_combination key
    exact blk_mem_range i _ (hvan _ hcommC).1 (hvan _ hcommC).2 hii
  have hq : CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 3) K) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple 3 K
      (by norm_num) (Or.inl (by norm_num)) (Or.inl (by norm_num))
  have hinj : Function.Injective (blk_sl (K := K) i) := blk_sl_injective i
  have hqH : CFSG.IsQuasisimple (blk_H (K := K) i) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective hinj) hq
  have hcard : Nat.card (blk_H (K := K) i) = 60480 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := K) (n := 3)
        (by norm_num), hK]
    first
    | decide
    | rfl
    | norm_num [Finset.prod_Icc_succ_top]
  unfold CentQuasi
  exact Or.inr ⟨blk_H i, hHC, hcomm, hqH, ⟨d, hdH, hd1, hd3, hdcen⟩, dvd_of_eq hcard⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK429.RowV
