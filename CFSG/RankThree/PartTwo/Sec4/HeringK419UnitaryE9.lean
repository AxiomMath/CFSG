module

public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartTwo.Sec4.HeringUnitary

open CFSG.Assembly.RankThreeEven (projSU)

theorem two_pow_mod_three_of_odd {m : ℕ} (hm : Odd m) : (2 : ℕ) ^ m % 3 = 2 := by
  obtain ⟨j, rfl⟩ := hm
  induction j with
  | zero => norm_num
  | succ k ih =>
    have e : (2 : ℕ) ^ (2 * (k + 1) + 1) = 4 * 2 ^ (2 * k + 1) := by ring
    rw [e, Nat.mul_mod, ih]

theorem exists_unit_cube_ne_one {m : ℕ} (hm : Odd m) :
    ∃ ω : (GaloisField 2 (2 * m))ˣ, ω ^ 3 = 1 ∧ ω ≠ 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hm0 : 0 < m := hm.pos
  have hcard : Nat.card (GaloisField 2 (2 * m)) = 2 ^ (2 * m) :=
    GaloisField.card 2 (2 * m) (by omega)
  have hpow : (2 : ℕ) ^ (2 * m) = 4 ^ m := by
    rw [pow_mul]; norm_num
  have h4 : (4 : ℕ) ^ m % 3 = 1 := by
    rw [Nat.pow_mod]; norm_num
  have hdvd : 3 ∣ Nat.card (GaloisField 2 (2 * m))ˣ := by
    rw [Nat.card_units, hcard, hpow]
    omega
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := (GaloisField 2 (2 * m))ˣ) 3 hdvd
  refine ⟨ω, ?_, fun h => ?_⟩
  · rw [← hω]
    exact pow_orderOf_eq_one ω
  · rw [h, orderOf_one] at hω
    norm_num at hω

theorem det_diag_three {K : Type*} [Field K] {w : K} (hw : w ^ 3 = 1) :
    Matrix.det (!![1, 0, 0; 0, w, 0; 0, 0, w ^ 2] : Matrix (Fin 3) (Fin 3) K) = 1 := by
  rw [Matrix.det_fin_three]
  simp
  linear_combination hw

theorem det_perm_three {K : Type*} [Field K] :
    Matrix.det (!![0, 1, 0; 0, 0, 1; 1, 0, 0] : Matrix (Fin 3) (Fin 3) K) = 1 := by
  rw [Matrix.det_fin_three]
  simp

theorem exists_gl_of_det_one {K : Type*} [Field K] (M : Matrix (Fin 3) (Fin 3) K)
    (h : Matrix.det M = 1) :
    ∃ g : Matrix.GeneralLinearGroup (Fin 3) K, (g : Matrix (Fin 3) (Fin 3) K) = M :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [h]; exact one_ne_zero), rfl⟩

theorem diag_cond {K : Type*} [Field K] {Q : ℕ} (hQ : Q ≠ 0) {w : K} (hw : w ^ 3 = 1)
    (hwQ : w ^ Q = w ^ 2) (hwQ2 : (w ^ 2) ^ Q = w ^ 4) :
    ((!![1, 0, 0; 0, w, 0; 0, 0, w ^ 2] : Matrix (Fin 3) (Fin 3) K).map (· ^ Q)).transpose *
      (!![1, 0, 0; 0, w, 0; 0, 0, w ^ 2] : Matrix (Fin 3) (Fin 3) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, hQ, hwQ, hwQ2] <;>
    first | ring1 | linear_combination hw | linear_combination (w ^ 3 + 1) * hw

theorem perm_cond {K : Type*} [Field K] {Q : ℕ} (hQ : Q ≠ 0) :
    ((!![0, 1, 0; 0, 0, 1; 1, 0, 0] : Matrix (Fin 3) (Fin 3) K).map (· ^ Q)).transpose *
      (!![0, 1, 0; 0, 0, 1; 1, 0, 0] : Matrix (Fin 3) (Fin 3) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, hQ]

theorem diag_pow_three {K : Type*} [Field K] {w : K} (hw : w ^ 3 = 1) :
    (!![1, 0, 0; 0, w, 0; 0, 0, w ^ 2] : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_three, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first | ring1 | linear_combination hw | linear_combination (w ^ 3 + 1) * hw

theorem perm_pow_three {K : Type*} [Field K] :
    (!![0, 1, 0; 0, 0, 1; 1, 0, 0] : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_three, Matrix.mul_apply, Fin.sum_univ_three]

theorem diag_perm_comm {K : Type*} [Field K] {w : K} (hw : w ^ 3 = 1) :
    (!![1, 0, 0; 0, w, 0; 0, 0, w ^ 2] : Matrix (Fin 3) (Fin 3) K) *
        (!![0, 1, 0; 0, 0, 1; 1, 0, 0] : Matrix (Fin 3) (Fin 3) K) * Matrix.scalar (Fin 3) w =
      (!![0, 1, 0; 0, 0, 1; 1, 0, 0] : Matrix (Fin 3) (Fin 3) K) *
        (!![1, 0, 0; 0, w, 0; 0, 0, w ^ 2] : Matrix (Fin 3) (Fin 3) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.scalar_apply, Matrix.diagonal_apply] <;>
    first | ring1 | linear_combination hw | linear_combination (w ^ 3 + 1) * hw

theorem mk_ne_of_entry {K : Type*} [Field K] (P Q : Matrix.GeneralLinearGroup (Fin 3) K)
    (hP : (P : Matrix (Fin 3) (Fin 3) K) = !![0, 1, 0; 0, 0, 1; 1, 0, 0])
    (hQ : (Q : Matrix (Fin 3) (Fin 3) K) 0 1 = 0) :
    Matrix.ProjGenLinGroup.mk P ≠ Matrix.ProjGenLinGroup.mk Q := by
  intro h
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h
  have e := congrArg (fun A : Matrix.GeneralLinearGroup (Fin 3) K =>
    (A : Matrix (Fin 3) (Fin 3) K) 0 1) hu
  have e' : (u : K) = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three, Matrix.scalar_apply, Matrix.diagonal_apply,
      hP, hQ] using e
  exact u.ne_zero e'

theorem mk_diag_ne_one {K : Type*} [Field K] {w : K} (hw : w ≠ 1)
    (d : Matrix.GeneralLinearGroup (Fin 3) K)
    (hd : (d : Matrix (Fin 3) (Fin 3) K) = !![1, 0, 0; 0, w, 0; 0, 0, w ^ 2]) :
    Matrix.ProjGenLinGroup.mk d ≠ 1 := by
  intro h
  rw [← map_one Matrix.ProjGenLinGroup.mk] at h
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h
  have e00 := congrArg (fun A : Matrix.GeneralLinearGroup (Fin 3) K =>
    (A : Matrix (Fin 3) (Fin 3) K) 0 0) hu
  have e11 := congrArg (fun A : Matrix.GeneralLinearGroup (Fin 3) K =>
    (A : Matrix (Fin 3) (Fin 3) K) 1 1) hu
  simp [hd, Matrix.mul_apply, Fin.sum_univ_three, Matrix.scalar_apply,
    Matrix.diagonal_apply] at e00 e11
  have hu1 : (u : K) = 1 := by simpa using e00
  apply hw
  simpa [hu1] using e11

theorem mk_mem_projSU {m : ℕ} (g : Matrix.GeneralLinearGroup (Fin 3) (GaloisField 2 (2 * m)))
    (hdet : Matrix.GeneralLinearGroup.det g = 1)
    (hg : ((g : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * m))).map (· ^ (2 ^ m))).transpose *
      (g : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * m))) = 1) :
    Matrix.ProjGenLinGroup.mk g ∈ projSU 3 2 m := by
  refine Subgroup.mem_map.mpr ⟨g, Subgroup.subset_closure ?_, rfl⟩
  exact ⟨hdet, hg⟩

theorem mem_zpowers_three_cases {G : Type*} [Group G] {x y : G} (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) (hy : y ∈ Subgroup.zpowers x) : y = 1 ∨ y = x ∨ y = x ^ 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
  have h3 : ((orderOf x : ℕ) : ℤ) = 3 := by rw [hord]; norm_num
  rw [← zpow_mod_orderOf, h3] at hk
  have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hk3 with h | h | h
  · left
    rw [← hk, h, zpow_zero]
  · right; left
    rw [← hk, h, zpow_one]
  · right; right
    simp [← hk, h]

theorem exists_commuting_order_three_projSU {m : ℕ} (hm : Odd m) :
    ∃ x y : projSU 3 2 m, x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x ≠ 1 ∧ x * y = y * x ∧
      y ∉ Subgroup.zpowers x := by
  obtain ⟨ω, hω3, hω1⟩ := exists_unit_cube_ne_one hm
  have hQ0 : (2 : ℕ) ^ m ≠ 0 := by positivity
  have hQmod : (2 : ℕ) ^ m % 3 = 2 := two_pow_mod_three_of_odd hm
  have hw3 : (ω : GaloisField 2 (2 * m)) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hω3, Units.val_one]
  have hw1 : (ω : GaloisField 2 (2 * m)) ≠ 1 := fun h => hω1 (Units.val_eq_one.mp h)
  have hwQ : (ω : GaloisField 2 (2 * m)) ^ (2 ^ m) = (ω : GaloisField 2 (2 * m)) ^ 2 := by
    have e : (2 : ℕ) ^ m = 3 * (2 ^ m / 3) + 2 := by omega
    rw [e, pow_add, pow_mul, hw3, one_pow, one_mul]
  have hwQ2 : ((ω : GaloisField 2 (2 * m)) ^ 2) ^ (2 ^ m) =
      (ω : GaloisField 2 (2 * m)) ^ 4 := by
    rw [pow_right_comm, hwQ]
    ring
  obtain ⟨d, hd⟩ := exists_gl_of_det_one
    (!![1, 0, 0; 0, (ω : GaloisField 2 (2 * m)), 0; 0, 0, (ω : GaloisField 2 (2 * m)) ^ 2])
    (det_diag_three hw3)
  obtain ⟨P, hP⟩ := exists_gl_of_det_one
    (!![0, 1, 0; 0, 0, 1; 1, 0, 0] : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * m)))
    det_perm_three
  have hdet_d : Matrix.GeneralLinearGroup.det d = 1 := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, hd, Units.val_one]
    exact det_diag_three hw3
  have hdet_P : Matrix.GeneralLinearGroup.det P = 1 := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, hP, Units.val_one]
    exact det_perm_three
  have hd3 : d ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hd, Units.val_one]
    exact diag_pow_three hw3
  have hP3 : P ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hP, Units.val_one]
    exact perm_pow_three
  have hdmem : Matrix.ProjGenLinGroup.mk d ∈ projSU 3 2 m :=
    mk_mem_projSU d hdet_d (by rw [hd]; exact diag_cond hQ0 hw3 hwQ hwQ2)
  have hPmem : Matrix.ProjGenLinGroup.mk P ∈ projSU 3 2 m :=
    mk_mem_projSU P hdet_P (by rw [hP]; exact perm_cond hQ0)
  obtain ⟨x, hx⟩ : ∃ x : projSU 3 2 m,
      (x : Matrix.ProjGenLinGroup (Fin 3) (GaloisField 2 (2 * m))) =
        Matrix.ProjGenLinGroup.mk d :=
    ⟨⟨_, hdmem⟩, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : projSU 3 2 m,
      (y : Matrix.ProjGenLinGroup (Fin 3) (GaloisField 2 (2 * m))) =
        Matrix.ProjGenLinGroup.mk P :=
    ⟨⟨_, hPmem⟩, rfl⟩
  have hx3 : x ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hx, ← map_pow Matrix.ProjGenLinGroup.mk d 3, hd3, map_one,
      Subgroup.coe_one]
  have hy3 : y ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hy, ← map_pow Matrix.ProjGenLinGroup.mk P 3, hP3, map_one,
      Subgroup.coe_one]
  have hx1 : x ≠ 1 := by
    intro h
    apply mk_diag_ne_one hw1 d hd
    rw [← hx, h, Subgroup.coe_one]
  have hcomm : d * P * Matrix.GeneralLinearGroup.scalar (Fin 3) ω = P * d := by
    apply Units.ext
    simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, hd, hP]
    exact diag_perm_comm hw3
  have hxy : x * y = y * x := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hx, hy, ← map_mul Matrix.ProjGenLinGroup.mk d P,
      ← map_mul Matrix.ProjGenLinGroup.mk P d]
    exact Matrix.ProjGenLinGroup.mk_eq_mk_iff.mpr ⟨ω, hcomm⟩
  refine ⟨x, y, hx3, hy3, hx1, hxy, ?_⟩
  intro hmem
  have hd01 : (d : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * m))) 0 1 = 0 := by
    rw [hd]
    simp
  have hd2 : ((d ^ 2 : Matrix.GeneralLinearGroup (Fin 3) (GaloisField 2 (2 * m))) :
      Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * m))) 0 1 = 0 := by
    rw [sq, Matrix.GeneralLinearGroup.coe_mul, hd]
    simp [Matrix.mul_apply, Fin.sum_univ_three]
  rcases mem_zpowers_three_cases hx3 hx1 hmem with h | h | h
  · have h' : Matrix.ProjGenLinGroup.mk P = Matrix.ProjGenLinGroup.mk 1 := by
      rw [map_one, ← hy, h, Subgroup.coe_one]
    exact mk_ne_of_entry P 1 hP (by simp) h'
  · have h' : Matrix.ProjGenLinGroup.mk P = Matrix.ProjGenLinGroup.mk d := by
      rw [← hy, ← hx, h]
    exact mk_ne_of_entry P d hP hd01 h'
  · have h' : Matrix.ProjGenLinGroup.mk P = Matrix.ProjGenLinGroup.mk (d ^ 2) := by
      rw [map_pow, ← hy, ← hx, h, Subgroup.coe_pow]
    exact mk_ne_of_entry P (d ^ 2) hP hd2 h'

end CFSG.RankThree.PartTwo.Sec4.HeringUnitary
