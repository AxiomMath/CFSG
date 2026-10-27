module

public import CFSG.RankThree.PartTwo.Sec4.Item424Res3ProofTools
public import CFSG.ClassicalInvolution.Phan.Blocks

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item424Res3

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.ClassicalInvolution Matrix
open scoped commutatorElement

section Center

variable {F : Type*} [Field F] {n : ℕ}

theorem not_mem_center_of_apply_ne_zero {A : Matrix.SpecialLinearGroup (Fin n) F} {i j : Fin n}
    (hij : i ≠ j) (hA : (A : Matrix (Fin n) (Fin n) F) i j ≠ 0) :
    A ∉ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F) := by
  intro hc
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  apply hA
  rw [← hr, scalar_apply, diagonal_apply_ne _ hij]

theorem not_mem_center_of_apply_ne {A : Matrix.SpecialLinearGroup (Fin n) F} {i j : Fin n}
    (hA : (A : Matrix (Fin n) (Fin n) F) i i ≠ (A : Matrix (Fin n) (Fin n) F) j j) :
    A ∉ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F) := by
  intro hc
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  apply hA
  rw [← hr, scalar_apply, diagonal_apply_eq, diagonal_apply_eq]

theorem exists_pow_eq_zpow_of_pow_three {M : Type*} [Group M] {x : M} (hx : x ^ 3 = 1) (k : ℤ) :
    ∃ m : ℕ, m < 3 ∧ x ^ k = x ^ m := by
  have h0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
  have h3 : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
  refine ⟨(k % 3).toNat, by omega, ?_⟩
  have h1 : x ^ k = x ^ (k % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 3]
    rw [_root_.zpow_add, _root_.zpow_mul, show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast,
      hx, _root_.one_zpow, mul_one]
  rw [h1, ← zpow_natCast, Int.toNat_of_nonneg h0]

theorem mul_inv_zpow_not_mem_center {x y : Matrix.SpecialLinearGroup (Fin n) F} (hx3 : x ^ 3 = 1)
    {i j : Fin n}
    (hx : ∀ m : ℕ, m < 3 →
      ((x ^ m : Matrix.SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = 0)
    (hy : (y : Matrix (Fin n) (Fin n) F) i j ≠ 0) (k : ℤ) :
    y * (x ^ k)⁻¹ ∉ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F) := by
  intro hc
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  obtain ⟨m, hm, hk⟩ := exists_pow_eq_zpow_of_pow_three hx3 k
  have hy' : y = (y * (x ^ k)⁻¹) * x ^ m := by rw [← hk]; group
  apply hy
  rw [hy', Matrix.SpecialLinearGroup.coe_mul, ← hr, scalar_apply, diagonal_mul, hx m hm, mul_zero]

end Center

section Blocks

variable {F : Type*} [Field F] {n : ℕ}

variable (F) in
@[expose] def mThree : Matrix (Fin 2) (Fin 2) F :=
  !![0, 1; -1, -1]

theorem det_mThree : (mThree F).det = 1 := by
  simp [mThree, det_fin_two]

theorem mThree_pow_three : mThree F ^ 3 = 1 := by
  rw [pow_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mThree, mul_apply, Fin.sum_univ_two]

variable (F) in
@[expose] def blkThree (n a : ℕ) (h : a + 2 ≤ n) : Matrix.SpecialLinearGroup (Fin n) F :=
  ⟨Phan.blockMat n a (mThree F), by rw [Phan.det_blockMat h, det_mThree]⟩

theorem coe_blkThree_pow {a : ℕ} (h : a + 2 ≤ n) (m : ℕ) :
    ((blkThree F n a h ^ m : Matrix.SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      Phan.blockMat n a (mThree F ^ m) := by
  induction m with
  | zero => rw [pow_zero, pow_zero, Matrix.SpecialLinearGroup.coe_one, Phan.blockMat_one]
  | succ m ih =>
    rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, ih, pow_succ, Phan.blockMat_mul h]
    rfl

theorem blkThree_pow_three {a : ℕ} (h : a + 2 ≤ n) : blkThree F n a h ^ 3 = 1 := by
  apply Subtype.ext
  rw [coe_blkThree_pow h, mThree_pow_three, Phan.blockMat_one, Matrix.SpecialLinearGroup.coe_one]

theorem blkThree_comm (h0 : 0 + 2 ≤ n) (h2 : 2 + 2 ≤ n) :
    blkThree F n 0 h0 * blkThree F n 2 h2 = blkThree F n 2 h2 * blkThree F n 0 h0 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  exact Phan.blockMat_comm (Or.inl (by omega)) _ _

theorem false_of_isType424_sl_four {X : Type} [Group X] [Finite X] (hT : Sec11.IsType424 X)
    (hQ : IsQuasisimple X) (hn : 4 ≤ n) (ψ : Matrix.SpecialLinearGroup (Fin n) F →* X)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F)) : False := by
  have h0 : 0 + 2 ≤ n := by omega
  have h2 : 2 + 2 ≤ n := by omega
  set x := blkThree F n 0 h0 with hx
  set y := blkThree F n 2 h2 with hy
  have hxy : ⁅x, y⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (blkThree_comm h0 h2)
  have hi : Phan.blockIdx 2 h2 (0 : Fin 2) ≠ Phan.blockIdx 2 h2 1 := fun h =>
    absurd ((Phan.blockIdx_injective h2) h) (by decide)
  refine false_of_isType424_map_pair hT hQ ψ hker (blkThree_pow_three h0)
    (blkThree_pow_three h2) (by rw [hxy]; exact Commute.one_left _)
    (by rw [hxy]; exact Commute.one_left _) ?_
    (mul_inv_zpow_not_mem_center (blkThree_pow_three h0) (i := Phan.blockIdx 2 h2 0)
      (j := Phan.blockIdx 2 h2 1) (fun m _ => ?_) ?_)
  · refine not_mem_center_of_apply_ne_zero (i := Phan.blockIdx 0 h0 0) (j := Phan.blockIdx 0 h0 1)
      (fun h => absurd ((Phan.blockIdx_injective h0) h) (by decide)) ?_
    change Phan.blockMat n 0 (mThree F) _ _ ≠ 0
    rw [Phan.blockMat_apply_blockIdx]
    simp [mThree]
  · rw [coe_blkThree_pow h0, Phan.blockMat_apply_of_not_mem_left _ (by simp), one_apply_ne hi]
  · change Phan.blockMat n 2 (mThree F) _ _ ≠ 0
    rw [Phan.blockMat_apply_blockIdx]
    simp [mThree]

end Blocks

section Transvections

variable {F : Type*} [Field F]

variable (F) in
@[expose] def tvA : Matrix.SpecialLinearGroup (Fin 3) F :=
  ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by simp [det_fin_three]⟩

variable (F) in
@[expose] def tvB : Matrix.SpecialLinearGroup (Fin 3) F :=
  ⟨!![1, 0, 1; 0, 1, 0; 0, 0, 1], by simp [det_fin_three]⟩

theorem tvA_pow_three (h3 : (3 : F) = 0) : tvA F ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, pow_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tvA, mul_apply, Fin.sum_univ_three]
  linear_combination h3

theorem tvB_pow_three (h3 : (3 : F) = 0) : tvB F ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, pow_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tvB, mul_apply, Fin.sum_univ_three]
  linear_combination h3

theorem tvA_comm_tvB : tvA F * tvB F = tvB F * tvA F := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tvA, tvB, mul_apply, Fin.sum_univ_three]

theorem tvA_pow_apply_zero_two {m : ℕ} (hm : m < 3) :
    ((tvA F ^ m : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 2 = 0 := by
  rw [Matrix.SpecialLinearGroup.coe_pow]
  interval_cases m <;> simp [tvA, pow_succ, mul_apply, Fin.sum_univ_three]

theorem false_of_isType424_sl_three_char_three {X : Type} [Group X] [Finite X]
    (hT : Sec11.IsType424 X) (hQ : IsQuasisimple X) (h3 : (3 : F) = 0)
    (ψ : Matrix.SpecialLinearGroup (Fin 3) F →* X)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F)) : False := by
  have hxy : ⁅tvA F, tvB F⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr tvA_comm_tvB
  refine false_of_isType424_map_pair hT hQ ψ hker (tvA_pow_three h3) (tvB_pow_three h3)
    (by rw [hxy]; exact Commute.one_left _) (by rw [hxy]; exact Commute.one_left _) ?_
    (mul_inv_zpow_not_mem_center (tvA_pow_three h3) (i := 0) (j := 2)
      (fun m hm => tvA_pow_apply_zero_two hm) (by simp [tvB]))
  exact not_mem_center_of_apply_ne_zero (i := 0) (j := 1) (by decide) (by simp [tvA])

end Transvections

section Diagonal

variable {F : Type*} [Field F]

@[expose] def dgW {ω : F} (hω : ω ^ 3 = 1) : Matrix.SpecialLinearGroup (Fin 3) F :=
  ⟨diagonal ![ω, ω ^ 2, 1], by
    rw [det_diagonal, Fin.prod_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, mul_one]
    rw [← pow_succ', hω]⟩

@[expose] def scW {ω : F} (hω : ω ^ 3 = 1) : Matrix.SpecialLinearGroup (Fin 3) F :=
  ⟨scalar (Fin 3) ω, by
    rw [scalar_apply, det_diagonal, Fin.prod_univ_three, ← hω]
    ring⟩

variable (F) in
@[expose] def cyc : Matrix.SpecialLinearGroup (Fin 3) F :=
  ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by simp [det_fin_three]⟩

theorem dgW_pow_three {ω : F} (hω : ω ^ 3 = 1) : dgW hω ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  change (diagonal ![ω, ω ^ 2, 1]) ^ 3 = 1
  rw [diagonal_pow, ← diagonal_one]
  have h6 : (ω ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hω, one_pow]
  congr 1
  funext i
  fin_cases i <;> simp [hω, h6]

theorem cyc_pow_three : cyc F ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, pow_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cyc, mul_apply, Fin.sum_univ_three]

theorem dgW_mul_cyc {ω : F} (hω : ω ^ 3 = 1) : dgW hω * cyc F = scW hω * (cyc F * dgW hω) := by
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  change (diagonal ![ω, ω ^ 2, 1] * !![(0 : F), 0, 1; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) F)
      i j = (scalar (Fin 3) ω * (!![(0 : F), 0, 1; 1, 0, 0; 0, 1, 0] *
        diagonal ![ω, ω ^ 2, 1]) : Matrix (Fin 3) (Fin 3) F) i j
  rw [diagonal_mul, scalar_apply, diagonal_mul, mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp
  · ring
  · rw [← hω]
    ring

theorem scW_mem_center {ω : F} (hω : ω ^ 3 = 1) :
    scW hω ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) :=
  Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨ω, by simpa using hω, rfl⟩

theorem commutator_dgW_cyc {ω : F} (hω : ω ^ 3 = 1) : ⁅dgW hω, cyc F⁆ = scW hω := by
  rw [commutatorElement_def, dgW_mul_cyc hω]
  group

theorem false_of_isType424_sl_three_root {X : Type} [Group X] [Finite X]
    (hT : Sec11.IsType424 X) (hQ : IsQuasisimple X) {ω : F} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (ψ : Matrix.SpecialLinearGroup (Fin 3) F →* X)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F)) : False := by
  have hc := commutator_dgW_cyc hω
  have hcen := scW_mem_center hω
  refine false_of_isType424_map_pair hT hQ ψ hker (dgW_pow_three hω) cyc_pow_three
    (by rw [hc]; exact (Subgroup.mem_center_iff.mp hcen _).symm)
    (by rw [hc]; exact (Subgroup.mem_center_iff.mp hcen _).symm) ?_
    (mul_inv_zpow_not_mem_center (dgW_pow_three hω) (i := 1) (j := 0) (fun m _ => ?_)
      (by simp [cyc]))
  · refine not_mem_center_of_apply_ne (i := 0) (j := 2) ?_
    simpa [dgW] using hω1
  · rw [Matrix.SpecialLinearGroup.coe_pow]
    change ((diagonal ![ω, ω ^ 2, 1]) ^ m) 1 0 = 0
    rw [diagonal_pow, diagonal_apply_ne _ (by decide)]

end Diagonal

theorem three_eq_zero_of_card_mod {F : Type*} [Field F] [Finite F] (h : Nat.card F % 3 = 0) :
    (3 : F) = 0 := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨p, hp⟩ := CharP.exists F
  obtain ⟨k, hpp, hk⟩ := FiniteField.card F p
  have h3 : 3 ∣ p ^ (k : ℕ) := by
    rw [← hk, ← Nat.card_eq_fintype_card]
    exact Nat.dvd_of_mod_eq_zero h
  have hp3 : p = 3 :=
    ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hpp).mp (Nat.prime_three.dvd_of_dvd_pow h3)).symm
  subst hp3
  exact_mod_cast CharP.cast_eq_zero F 3

theorem exists_cube_root_of_card_mod {F : Type*} [Field F] [Finite F] (h : Nat.card F % 3 = 1) :
    ∃ ω : F, ω ^ 3 = 1 ∧ ω ≠ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : 3 ∣ Nat.card Fˣ := by
    rw [Nat.card_units]
    have := Finite.one_lt_card (α := F)
    omega
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 3 h3
  refine ⟨u, ?_, fun h1 => ?_⟩
  · rw [← Units.val_pow_eq_pow_val, ← hu, pow_orderOf_eq_one, Units.val_one]
  · have hu1 : u = 1 := Units.ext h1
    rw [hu1, orderOf_one] at hu
    omega

theorem eq_three_and_mod_of_isType424 {F₀ : Type*} [Field F₀] [Finite F₀] {n : ℕ} (hn : 3 ≤ n)
    {X : Type} [Group X] [Finite X] (hT : Sec11.IsType424 X) (hQ : IsQuasisimple X)
    (ψ : Matrix.SpecialLinearGroup (Fin n) F₀ →* X)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F₀)) :
    n = 3 ∧ Nat.card F₀ % 3 = 2 := by
  by_cases h4 : 4 ≤ n
  · exact (false_of_isType424_sl_four hT hQ h4 ψ hker).elim
  obtain rfl : n = 3 := by omega
  refine ⟨rfl, ?_⟩
  rcases (by omega : Nat.card F₀ % 3 = 0 ∨ Nat.card F₀ % 3 = 1 ∨ Nat.card F₀ % 3 = 2) with
    h0 | h1 | h2
  · exact (false_of_isType424_sl_three_char_three hT hQ (three_eq_zero_of_card_mod h0) ψ
      hker).elim
  · obtain ⟨ω, hω, hω1⟩ := exists_cube_root_of_card_mod h1
    exact (false_of_isType424_sl_three_root hT hQ hω hω1 ψ hker).elim
  · exact h2

end CFSG.RankThree.PartTwo.Sec4.Item424Res3
