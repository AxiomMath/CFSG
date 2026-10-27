module

public import CFSG.RankThree.SubgroupLists.SymplecticTransvections

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K]

@[expose] def cliffMat (x y z b c : K) : Matrix V₄ V₄ K :=
  fromBlocks !![x, y; z, -x] !![0, b; -b, 0] !![0, c; -c, 0] !![x, z; y, -x]

theorem cliffMat_mul_self (x y z b c : K) :
    cliffMat x y z b c * cliffMat x y z b c = Matrix.scalar V₄ (x ^ 2 + y * z - b * c) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [cliffMat, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.scalar_apply] <;> ring

@[expose] def cliffSpace : Submodule K (Matrix V₄ V₄ K) where
  carrier := {Z | Zᵀ * spGram 2 K = spGram 2 K * Z ∧ Z.trace = 0}
  add_mem' := by
    rintro Z Y ⟨hZ, hZt⟩ ⟨hY, hYt⟩
    refine ⟨?_, ?_⟩
    · rw [transpose_add, Matrix.add_mul, Matrix.mul_add, hZ, hY]
    · rw [trace_add, hZt, hYt, add_zero]
  zero_mem' := by simp
  smul_mem' := by
    rintro c Z ⟨hZ, hZt⟩
    refine ⟨?_, ?_⟩
    · rw [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hZ]
    · rw [trace_smul, hZt, smul_zero]

theorem cliffMat_mem (x y z b c : K) : cliffMat x y z b c ∈ (cliffSpace : Submodule K _) := by
  refine ⟨?_, ?_⟩
  · ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [cliffMat, Matrix.mul_apply, Fintype.sum_sum_type, spGram, Matrix.one_apply]
  · simp [cliffMat, Matrix.trace, Fintype.sum_sum_type]

variable (h2 : (2 : K) ≠ 0)
include h2

theorem eq_cliffMat_of_mem {Z : Matrix V₄ V₄ K} (hZ : Z ∈ (cliffSpace : Submodule K _)) :
    Z = cliffMat (Z (Sum.inl 0) (Sum.inl 0)) (Z (Sum.inl 0) (Sum.inl 1))
      (Z (Sum.inl 1) (Sum.inl 0)) (Z (Sum.inl 0) (Sum.inr 1)) (Z (Sum.inr 0) (Sum.inl 1)) := by
  obtain ⟨hJ, ht⟩ := hZ
  have e : ∀ i j, (Zᵀ * spGram 2 K) i j = (spGram 2 K * Z) i j := fun i j => by rw [hJ]
  have e1 := e (Sum.inl 0) (Sum.inr 0)
  have e2 := e (Sum.inl 0) (Sum.inr 1)
  have e3 := e (Sum.inl 1) (Sum.inr 0)
  have e4 := e (Sum.inl 1) (Sum.inr 1)
  have e5 := e (Sum.inl 0) (Sum.inl 0)
  have e6 := e (Sum.inl 0) (Sum.inl 1)
  have e7 := e (Sum.inl 1) (Sum.inl 1)
  have e8 := e (Sum.inr 0) (Sum.inr 0)
  have e9 := e (Sum.inr 0) (Sum.inr 1)
  have e10 := e (Sum.inr 1) (Sum.inr 1)
  simp [Matrix.mul_apply, Fintype.sum_sum_type, spGram, Matrix.one_apply] at e1
  simp [Matrix.mul_apply, Fintype.sum_sum_type, spGram, Matrix.one_apply] at e2
  simp [Matrix.mul_apply, Fintype.sum_sum_type, spGram, Matrix.one_apply] at e3
  simp [Matrix.mul_apply, Fintype.sum_sum_type, spGram, Matrix.one_apply] at e4
  simp [Matrix.mul_apply, Fintype.sum_sum_type, spGram, Matrix.one_apply] at e5
  simp [Matrix.mul_apply, Fintype.sum_sum_type, spGram, Matrix.one_apply] at e6
  simp [Matrix.mul_apply, Fintype.sum_sum_type, spGram, Matrix.one_apply] at e7
  simp [Matrix.mul_apply, Fintype.sum_sum_type, spGram, Matrix.one_apply] at e8
  simp [Matrix.mul_apply, Fintype.sum_sum_type, spGram, Matrix.one_apply] at e9
  simp [Matrix.mul_apply, Fintype.sum_sum_type, spGram, Matrix.one_apply] at e10
  simp [Matrix.trace, Fintype.sum_sum_type] at ht
  have two_eq {a : K} (h : -a = a) : a = 0 := by
    have : (2 : K) * a = 0 := by linear_combination -h
    exact (mul_eq_zero.mp this).resolve_left h2
  have c00 : Z (Sum.inr 0) (Sum.inl 0) = 0 := two_eq e5
  have c11 : Z (Sum.inr 1) (Sum.inl 1) = 0 := two_eq e7
  have h00 : Z (Sum.inl 0) (Sum.inr 0) = 0 := two_eq (by linear_combination -e8)
  have h11 : Z (Sum.inl 1) (Sum.inr 1) = 0 := two_eq (by linear_combination -e10)
  have htr : Z (Sum.inl 1) (Sum.inl 1) = - Z (Sum.inl 0) (Sum.inl 0) := by
    have : (2 : K) * (Z (Sum.inl 0) (Sum.inl 0) + Z (Sum.inl 1) (Sum.inl 1)) = 0 := by
      linear_combination ht + e1 + e4
    have h' := (mul_eq_zero.mp this).resolve_left h2
    linear_combination h'
  have r1 : Z (Sum.inr 0) (Sum.inr 0) = Z (Sum.inl 0) (Sum.inl 0) := e1.symm
  have r2 : Z (Sum.inr 0) (Sum.inr 1) = Z (Sum.inl 1) (Sum.inl 0) := e2.symm
  have r3 : Z (Sum.inr 1) (Sum.inr 0) = Z (Sum.inl 0) (Sum.inl 1) := e3.symm
  have r4 : Z (Sum.inr 1) (Sum.inr 1) = - Z (Sum.inl 0) (Sum.inl 0) := by rw [← e4, htr]
  have r6 : Z (Sum.inr 1) (Sum.inl 0) = - Z (Sum.inr 0) (Sum.inl 1) := by
    linear_combination -e6
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [cliffMat, c00, c11, h00, h11, htr, r1, r2, r3, r4, r6, e9]

omit h2 in
@[expose] def cliffQ (Z : Matrix V₄ V₄ K) : K := (Z * Z) (Sum.inl 0) (Sum.inl 0)

theorem mul_self_of_mem {Z : Matrix V₄ V₄ K} (hZ : Z ∈ (cliffSpace : Submodule K _)) :
    Z * Z = cliffQ Z • (1 : Matrix V₄ V₄ K) := by
  have h := eq_cliffMat_of_mem h2 hZ
  have h' : cliffQ Z = (Z (Sum.inl 0) (Sum.inl 0)) ^ 2 +
      Z (Sum.inl 0) (Sum.inl 1) * Z (Sum.inl 1) (Sum.inl 0) -
      Z (Sum.inl 0) (Sum.inr 1) * Z (Sum.inr 0) (Sum.inl 1) := by
    rw [cliffQ, h, cliffMat_mul_self]
    simp [cliffMat]
  rw [h', h, cliffMat_mul_self, Matrix.smul_one_eq_diagonal]
  simp [cliffMat, Matrix.scalar_apply]

omit h2 in
@[expose] def cliffB (Z Y : Matrix V₄ V₄ K) : K :=
  (2 : K)⁻¹ * (Z * Y + Y * Z) (Sum.inl 0) (Sum.inl 0)

theorem mul_add_mul_of_mem {Z Y : Matrix V₄ V₄ K} (hZ : Z ∈ (cliffSpace : Submodule K _))
    (hY : Y ∈ (cliffSpace : Submodule K _)) :
    Z * Y + Y * Z = (2 * cliffB Z Y) • (1 : Matrix V₄ V₄ K) := by
  have hZY := mul_self_of_mem h2 (Submodule.add_mem _ hZ hY)
  have hZZ := mul_self_of_mem h2 hZ
  have hYY := mul_self_of_mem h2 hY
  have hsum : Z * Y + Y * Z = (cliffQ (Z + Y) - cliffQ Z - cliffQ Y) • (1 : Matrix V₄ V₄ K) := by
    rw [sub_smul, sub_smul, ← hZY, ← hZZ, ← hYY]
    noncomm_ring
  rw [hsum]
  congr 1
  rw [cliffB, hsum]
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
  field_simp

omit h2 in
theorem cliffB_comm (Z Y : Matrix V₄ V₄ K) : cliffB Z Y = cliffB Y Z := by
  rw [cliffB, cliffB, add_comm]

omit h2 in
theorem cliffB_add_left (Z Z' Y : Matrix V₄ V₄ K) :
    cliffB (Z + Z') Y = cliffB Z Y + cliffB Z' Y := by
  simp only [cliffB, Matrix.add_mul, Matrix.mul_add, Matrix.add_apply]
  ring

omit h2 in
theorem cliffB_smul_left (c : K) (Z Y : Matrix V₄ V₄ K) :
    cliffB (c • Z) Y = c * cliffB Z Y := by
  simp only [cliffB, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul]
  ring

theorem cliffB_self (Z : Matrix V₄ V₄ K) : cliffB Z Z = cliffQ Z := by
  rw [cliffB, cliffQ, Matrix.add_apply]
  field_simp
  ring

theorem mem_cliffSpace_of_involution {d : GL V₄ K} (hd : d ∈ StatedSp 2 K) (hd2 : d * d = 1)
    (hd1 : d ≠ 1) (hdm : d ≠ -1) :
    ((d : GL V₄ K) : Matrix V₄ V₄ K) ∈ (cliffSpace : Submodule K _) ∧
      cliffQ (d : Matrix V₄ V₄ K) = 1 := by
  have hdd : (d : Matrix V₄ V₄ K) * d = 1 := by rw [← Units.val_mul, hd2, Units.val_one]
  have hSp := transpose_mul_spGram_mul hd
  have hsa : (d : Matrix V₄ V₄ K)ᵀ * spGram 2 K = spGram 2 K * d := by
    calc (d : Matrix V₄ V₄ K)ᵀ * spGram 2 K
        = (d : Matrix V₄ V₄ K)ᵀ * spGram 2 K * ((d : Matrix V₄ V₄ K) * d) := by
          rw [hdd, Matrix.mul_one]
      _ = ((d : Matrix V₄ V₄ K)ᵀ * spGram 2 K * d) * d := (Matrix.mul_assoc _ _ _).symm
      _ = spGram 2 K * d := by rw [hSp]
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h2
  set l : K := (4 : K)⁻¹ * (d : Matrix V₄ V₄ K).trace with hl
  set Z : Matrix V₄ V₄ K := (d : Matrix V₄ V₄ K) - l • (1 : Matrix V₄ V₄ K) with hZdef
  have htr1 : (l • (1 : Matrix V₄ V₄ K)).trace = 4 * l := by
    simp [Matrix.trace]
  have hZ : Z ∈ (cliffSpace : Submodule K _) := by
    refine ⟨?_, ?_⟩
    · rw [hZdef, transpose_sub, Matrix.sub_mul, Matrix.mul_sub, hsa, transpose_smul,
        transpose_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    · rw [hZdef, trace_sub, htr1, hl]
      field_simp
      ring
  have hZZ := mul_self_of_mem h2 hZ
  have hdZ : (d : Matrix V₄ V₄ K) = Z + l • (1 : Matrix V₄ V₄ K) := by rw [hZdef]; abel
  have hkey : (2 * l) • Z = (1 - l ^ 2 - cliffQ Z) • (1 : Matrix V₄ V₄ K) := by
    have e : (Z + l • (1 : Matrix V₄ V₄ K)) * (Z + l • (1 : Matrix V₄ V₄ K)) =
        Z * Z + (2 * l) • Z + (l ^ 2) • (1 : Matrix V₄ V₄ K) := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.one_mul, Matrix.mul_one]
      module
    rw [← hdZ, hdd, hZZ] at e
    rw [sub_smul, sub_smul, one_smul]
    nth_rewrite 1 [e]
    abel
  have hl0 : l = 0 := by
    by_contra hl0
    have h2l : (2 : K) * l ≠ 0 := mul_ne_zero h2 hl0
    have hZs : Z = ((2 * l)⁻¹ * (1 - l ^ 2 - cliffQ Z)) • (1 : Matrix V₄ V₄ K) := by
      rw [mul_smul, ← hkey, smul_smul, inv_mul_cancel₀ h2l, one_smul]
    have htZ := hZ.2
    rw [hZs, Matrix.trace_smul, Matrix.trace_one, Fintype.card_sum, Fintype.card_fin,
      smul_eq_mul] at htZ
    have hc : (2 * l)⁻¹ * (1 - l ^ 2 - cliffQ Z) = 0 := by
      have : ((2 + 2 : ℕ) : K) ≠ 0 := by
        rw [Nat.cast_add, Nat.cast_ofNat]
        intro h
        apply h4
        linear_combination h
      exact (mul_eq_zero.mp htZ).resolve_right this
    rw [hc, zero_smul] at hZs
    rw [hZs, zero_add] at hdZ
    have hl2 : l ^ 2 = 1 := by
      have := congrFun (congrFun hdd (Sum.inl 0)) (Sum.inl 0)
      rw [hdZ] at this
      simp [Matrix.smul_apply, Matrix.mul_apply, Matrix.one_apply] at this
      linear_combination this
    have : (l - 1) * (l + 1) = 0 := by linear_combination hl2
    rcases mul_eq_zero.mp this with h | h
    · apply hd1
      apply Units.ext
      rw [hdZ, show l = 1 by linear_combination h, one_smul, Units.val_one]
    · apply hdm
      apply Units.ext
      rw [hdZ, show l = -1 by linear_combination h, neg_one_smul, Units.val_neg, Units.val_one]
  have hdZ' : (d : Matrix V₄ V₄ K) = Z := by rw [hdZ, hl0, zero_smul, add_zero]
  refine ⟨hdZ' ▸ hZ, ?_⟩
  rw [cliffQ, hdd]
  simp

omit h2 in
theorem conj_mem_cliffSpace {g : GL V₄ K} (hg : g ∈ StatedSp 2 K) {Z : Matrix V₄ V₄ K}
    (hZ : Z ∈ (cliffSpace : Submodule K _)) :
    (g : Matrix V₄ V₄ K) * Z * ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) ∈
      (cliffSpace : Submodule K _) := by
  obtain ⟨hJ, ht⟩ := hZ
  have hg' := transpose_mul_spGram_mul hg
  have hgi := transpose_mul_spGram_mul (inv_mem hg)
  have hgg : ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * g = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hgg' : (g : Matrix V₄ V₄ K) * ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e1 : (g : Matrix V₄ V₄ K)ᵀ * spGram 2 K =
      spGram 2 K * ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) := by
    calc (g : Matrix V₄ V₄ K)ᵀ * spGram 2 K
        = (g : Matrix V₄ V₄ K)ᵀ * spGram 2 K * ((g : Matrix V₄ V₄ K) *
            ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K)) := by rw [hgg', Matrix.mul_one]
      _ = ((g : Matrix V₄ V₄ K)ᵀ * spGram 2 K * g) * ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) := by
          simp only [Matrix.mul_assoc]
      _ = spGram 2 K * ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) := by rw [hg']
  have e2 : ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K)ᵀ * spGram 2 K = spGram 2 K * g := by
    calc ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K)ᵀ * spGram 2 K
        = ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K)ᵀ * spGram 2 K *
            (((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * g) := by rw [hgg, Matrix.mul_one]
      _ = (((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K)ᵀ * spGram 2 K * ((g⁻¹ : GL V₄ K) :
            Matrix V₄ V₄ K)) * g := by simp only [Matrix.mul_assoc]
      _ = spGram 2 K * g := by rw [hgi]
  refine ⟨?_, ?_⟩
  · rw [transpose_mul, transpose_mul]
    calc ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K)ᵀ * (Zᵀ * (g : Matrix V₄ V₄ K)ᵀ) * spGram 2 K
        = ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K)ᵀ * (Zᵀ * ((g : Matrix V₄ V₄ K)ᵀ * spGram 2 K)) := by
          simp only [Matrix.mul_assoc]
      _ = ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K)ᵀ * ((Zᵀ * spGram 2 K) *
            ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K)) := by rw [e1, Matrix.mul_assoc]
      _ = (((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K)ᵀ * spGram 2 K) * Z *
            ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) := by rw [hJ]; simp only [Matrix.mul_assoc]
      _ = spGram 2 K * ((g : Matrix V₄ V₄ K) * Z * ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K)) := by
          rw [e2]; simp only [Matrix.mul_assoc]
  · rw [Matrix.trace_mul_cycle, hgg, Matrix.one_mul, ht]

omit h2 in
theorem conj_mul_conj (g : GL V₄ K) (Z Y : Matrix V₄ V₄ K) :
    ((g : Matrix V₄ V₄ K) * Z * ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K)) *
        ((g : Matrix V₄ V₄ K) * Y * ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K)) =
      (g : Matrix V₄ V₄ K) * (Z * Y) * ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) := by
  have hgg : ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * g = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc ((g : Matrix V₄ V₄ K) * Z * ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K)) *
        ((g : Matrix V₄ V₄ K) * Y * ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K))
      = (g : Matrix V₄ V₄ K) * Z * (((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * g) * Y *
          ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) := by simp only [Matrix.mul_assoc]
    _ = (g : Matrix V₄ V₄ K) * (Z * Y) * ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) := by
        rw [hgg, Matrix.mul_one]; simp only [Matrix.mul_assoc]

omit h2 in
theorem conj_smul_one (g : GL V₄ K) (c : K) :
    (g : Matrix V₄ V₄ K) * (c • (1 : Matrix V₄ V₄ K)) * ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) =
      c • (1 : Matrix V₄ V₄ K) := by
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← Units.val_mul, mul_inv_cancel,
    Units.val_one]

theorem cliffB_conj (g : GL V₄ K) {Z Y : Matrix V₄ V₄ K} (hZ : Z ∈ (cliffSpace : Submodule K _))
    (hY : Y ∈ (cliffSpace : Submodule K _)) :
    cliffB ((g : Matrix V₄ V₄ K) * Z * ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K))
      ((g : Matrix V₄ V₄ K) * Y * ((g⁻¹ : GL V₄ K) : Matrix V₄ V₄ K)) = cliffB Z Y := by
  have h := mul_add_mul_of_mem h2 hZ hY
  rw [cliffB, conj_mul_conj, conj_mul_conj, ← Matrix.add_mul, ← Matrix.mul_add, h,
    conj_smul_one]
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
  field_simp

theorem mul_mul_eq_reflection {d Z : Matrix V₄ V₄ K} (hd : d ∈ (cliffSpace : Submodule K _))
    (hdd : d * d = 1) (hZ : Z ∈ (cliffSpace : Submodule K _)) :
    d * Z * d = (2 * cliffB d Z) • d - Z := by
  have h := mul_add_mul_of_mem h2 hd hZ
  calc d * Z * d = (d * Z + Z * d) * d - Z * (d * d) := by noncomm_ring
    _ = (2 * cliffB d Z) • d - Z := by rw [h, hdd, Matrix.smul_mul, Matrix.one_mul,
        Matrix.mul_one]

theorem mul_eq_neg_mul_iff {Z Y : Matrix V₄ V₄ K} (hZ : Z ∈ (cliffSpace : Submodule K _))
    (hY : Y ∈ (cliffSpace : Submodule K _)) : Z * Y = -(Y * Z) ↔ cliffB Z Y = 0 := by
  have h := mul_add_mul_of_mem h2 hZ hY
  constructor
  · intro hZY
    rw [hZY, neg_add_cancel] at h
    have := congrFun (congrFun h (Sum.inl 0)) (Sum.inl 0)
    simp at this
    rcases this with h' | h'
    · exact absurd h' h2
    · exact h'
  · intro hB
    rw [hB, mul_zero, zero_smul] at h
    exact eq_neg_of_add_eq_zero_left h

theorem mul_sq_of_involutions {d e : Matrix V₄ V₄ K} (hd : d ∈ (cliffSpace : Submodule K _))
    (he : e ∈ (cliffSpace : Submodule K _)) (hdd : d * d = 1) (hee : e * e = 1) :
    (d * e) * (d * e) = (2 * cliffB d e) • (d * e) - 1 := by
  have h := mul_add_mul_of_mem h2 he hd
  rw [cliffB_comm] at h
  calc (d * e) * (d * e) = d * (e * d + d * e) * e - (d * d) * (e * e) := by noncomm_ring
    _ = (2 * cliffB d e) • (d * e) - 1 := by
      rw [h, hdd, hee, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

end CFSG.RankThree.SubgroupLists
