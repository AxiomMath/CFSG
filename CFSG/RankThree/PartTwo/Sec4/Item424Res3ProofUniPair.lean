module

public import CFSG.RankThree.PartTwo.Sec4.Item424Res3ProofE9

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item424Res3

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo Matrix
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

variable {p f : ℕ} {K : Type} [Field K]

theorem su_ext {x y : unitarySU p f K 3}
    (hxy : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) : x = y :=
  Subtype.ext (Units.ext hxy)

theorem coe_su_mul (x y : unitarySU p f K 3) :
    (((x * y : unitarySU p f K 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := rfl

theorem coe_su_pow (x : unitarySU p f K 3) (m : ℕ) :
    (((x ^ m : unitarySU p f K 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ m := by
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]

theorem exists_scalar_of_mem_center_su (h : UnitaryFieldData p f K) (hq : 2 < p ^ f)
    {z : unitarySU p f K 3} (hz : z ∈ Subgroup.center (unitarySU p f K 3)) :
    ∃ c : K, ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c := by
  rw [KFacts.center_unitarySU_three (h := h) hq] at hz
  obtain ⟨c, -, -, hc⟩ := mem_unitaryScalars.mp hz
  exact ⟨c, by rw [hc, GeneralLinearGroup.coe_scalar]⟩

theorem su_not_mem_center_of_apply_ne_zero (h : UnitaryFieldData p f K) (hq : 2 < p ^ f)
    {A : unitarySU p f K 3} {i j : Fin 3} (hij : i ≠ j)
    (hA : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j ≠ 0) :
    A ∉ Subgroup.center (unitarySU p f K 3) := by
  intro hc
  obtain ⟨c, hc'⟩ := exists_scalar_of_mem_center_su h hq hc
  apply hA
  rw [hc', scalar_apply, diagonal_apply_ne _ hij]

theorem su_not_mem_center_of_apply_ne (h : UnitaryFieldData p f K) (hq : 2 < p ^ f)
    {A : unitarySU p f K 3} {i j : Fin 3}
    (hA : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i i ≠
      ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) j j) :
    A ∉ Subgroup.center (unitarySU p f K 3) := by
  intro hc
  obtain ⟨c, hc'⟩ := exists_scalar_of_mem_center_su h hq hc
  apply hA
  rw [hc', scalar_apply, diagonal_apply_eq, diagonal_apply_eq]

theorem su_mul_inv_zpow_not_mem_center (h : UnitaryFieldData p f K) (hq : 2 < p ^ f)
    {x y : unitarySU p f K 3} (hx3 : x ^ 3 = 1)
    (hxy : ∀ m : ℕ, m < 3 → ∃ i j : Fin 3,
      (((x ^ m : unitarySU p f K 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j = 0 ∧
        ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j ≠ 0)
    (k : ℤ) : y * (x ^ k)⁻¹ ∉ Subgroup.center (unitarySU p f K 3) := by
  intro hc
  obtain ⟨c, hc'⟩ := exists_scalar_of_mem_center_su h hq hc
  obtain ⟨m, hm, hk⟩ := exists_pow_eq_zpow_of_pow_three hx3 k
  obtain ⟨i, j, hxij, hyij⟩ := hxy m hm
  have hy' : y = (y * (x ^ k)⁻¹) * x ^ m := by rw [← hk]; group
  apply hyij
  rw [hy', coe_su_mul, hc', scalar_apply, diagonal_mul, hxij, mul_zero]

variable (h : UnitaryFieldData p f K)

@[expose] noncomputable def cycU : unitarySU p f K 3 :=
  ⟨GeneralLinearGroup.mkOfDetNeZero !![0, 0, 1; 1, 0, 0; 0, 1, 0] (by simp [det_fin_three]),
    (mem_unitarySU_iff h).mpr ⟨by simp [det_fin_three], by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]⟩⟩

theorem coe_cycU :
    ((cycU h : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = !![0, 0, 1; 1, 0, 0; 0, 1, 0] :=
  rfl

theorem cycU_pow_three : cycU h ^ 3 = 1 := by
  apply su_ext
  rw [coe_su_pow, coe_cycU, pow_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]

variable {h}

@[expose] noncomputable def dgU {ω : K} (hω : ω ^ 3 = 1) (hωb : h.bar ω * ω = 1) :
    unitarySU p f K 3 :=
  ⟨GeneralLinearGroup.mkOfDetNeZero (diagonal ![ω, ω ^ 2, 1]) (by
      rw [det_diagonal, Fin.prod_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, mul_one]
      rw [← pow_succ', hω]
      exact one_ne_zero),
    (mem_unitarySU_iff h).mpr ⟨by
      change (diagonal ![ω, ω ^ 2, 1]).det = 1
      rw [det_diagonal, Fin.prod_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, mul_one]
      rw [← pow_succ', hω], by
      change ((diagonal ![ω, ω ^ 2, 1]).map h.bar)ᵀ * diagonal ![ω, ω ^ 2, 1] = 1
      have h2 : h.bar ω ^ 2 * ω ^ 2 = 1 := by rw [← mul_pow, hωb, one_pow]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [mul_apply, diagonal, hωb, h2]⟩⟩

theorem coe_dgU {ω : K} (hω : ω ^ 3 = 1) (hωb : h.bar ω * ω = 1) :
    ((dgU hω hωb : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![ω, ω ^ 2, 1] :=
  rfl

@[expose] noncomputable def scU {ω : K} (hω : ω ^ 3 = 1) (hωb : h.bar ω * ω = 1) :
    unitarySU p f K 3 :=
  ⟨GeneralLinearGroup.mkOfDetNeZero (scalar (Fin 3) ω) (by
      rw [scalar_apply, det_diagonal, Fin.prod_univ_three]
      have : ω * ω * ω = 1 := by rw [← hω]; ring
      rw [this]
      exact one_ne_zero),
    (mem_unitarySU_iff h).mpr ⟨by
      change (scalar (Fin 3) ω).det = 1
      rw [scalar_apply, det_diagonal, Fin.prod_univ_three, ← hω]
      ring, by
      change ((scalar (Fin 3) ω).map h.bar)ᵀ * scalar (Fin 3) ω = 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [mul_apply, scalar_apply, diagonal, hωb]⟩⟩

theorem scU_mem_center {ω : K} (hω : ω ^ 3 = 1) (hωb : h.bar ω * ω = 1) :
    scU hω hωb ∈ Subgroup.center (unitarySU p f K 3) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply su_ext
  rw [coe_su_mul, coe_su_mul]
  change ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * scalar (Fin 3) ω =
    scalar (Fin 3) ω * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  exact ((Matrix.scalar_commute ω (fun r => Commute.all ω r) _)).eq.symm

theorem dgU_pow_three {ω : K} (hω : ω ^ 3 = 1) (hωb : h.bar ω * ω = 1) :
    dgU hω hωb ^ 3 = 1 := by
  apply su_ext
  rw [coe_su_pow, coe_dgU, diagonal_pow]
  change diagonal (![ω, ω ^ 2, 1] ^ 3) = 1
  rw [← diagonal_one]
  have h6 : (ω ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hω, one_pow]
  congr 1
  funext i
  fin_cases i <;> simp [hω, h6]

theorem dgU_mul_cycU {ω : K} (hω : ω ^ 3 = 1) (hωb : h.bar ω * ω = 1) :
    dgU hω hωb * cycU h = scU hω hωb * (cycU h * dgU hω hωb) := by
  apply su_ext
  rw [coe_su_mul, coe_su_mul, coe_su_mul, coe_dgU, coe_cycU]
  change (diagonal ![ω, ω ^ 2, 1] * !![(0 : K), 0, 1; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) K)
    = scalar (Fin 3) ω * (!![(0 : K), 0, 1; 1, 0, 0; 0, 1, 0] * diagonal ![ω, ω ^ 2, 1])
  ext i j
  rw [diagonal_mul, scalar_apply, diagonal_mul, mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp
  · ring
  · rw [← hω]
    ring

@[expose] noncomputable def tvU (h3 : (3 : K) = 0) {a : K} (ha : h.bar a = -a) :
    unitarySU p f K 3 :=
  ⟨GeneralLinearGroup.mkOfDetNeZero !![1 + a, a, a; a, 1 + a, a; a, a, 1 + a] (by
      have : (!![1 + a, a, a; a, 1 + a, a; a, a, 1 + a] : Matrix (Fin 3) (Fin 3) K).det = 1 := by
        rw [det_fin_three]
        simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
          Matrix.tail_cons, Matrix.head_fin_const]
        linear_combination a * h3
      rw [this]
      exact one_ne_zero),
    (mem_unitarySU_iff h).mpr ⟨by
      change (!![1 + a, a, a; a, 1 + a, a; a, a, 1 + a] : Matrix (Fin 3) (Fin 3) K).det = 1
      rw [det_fin_three]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
        Matrix.tail_cons, Matrix.head_fin_const]
      linear_combination a * h3, by
      change ((!![1 + a, a, a; a, 1 + a, a; a, a, 1 + a] : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ *
        !![1 + a, a, a; a, 1 + a, a; a, a, 1 + a] = 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, ha] <;>
        linear_combination (-a ^ 2) * h3⟩⟩

theorem coe_tvU (h3 : (3 : K) = 0) {a : K} (ha : h.bar a = -a) :
    ((tvU h3 ha : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![1 + a, a, a; a, 1 + a, a; a, a, 1 + a] :=
  rfl

theorem tvU_pow_three (h3 : (3 : K) = 0) {a : K} (ha : h.bar a = -a) : tvU h3 ha ^ 3 = 1 := by
  apply su_ext
  rw [coe_su_pow, coe_tvU, pow_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three] <;>
    linear_combination (a + 3 * a ^ 2 + 3 * a ^ 3) * h3

theorem cycU_mul_tvU (h3 : (3 : K) = 0) {a : K} (ha : h.bar a = -a) :
    cycU h * tvU h3 ha = tvU h3 ha * cycU h := by
  apply su_ext
  rw [coe_su_mul, coe_su_mul, coe_tvU, coe_cycU]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]

theorem false_of_isType424_su_two {X : Type} [Group X] [Finite X] (hT : Sec11.IsType424 X)
    (hQ : IsQuasisimple X) (hq : 2 < p ^ f) {ω : K} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (hωb : h.bar ω * ω = 1) (ψ : unitarySU p f K 3 →* X)
    (hker : ψ.ker ≤ Subgroup.center (unitarySU p f K 3)) : False := by
  have hc : ⁅dgU hω hωb, cycU h⁆ = scU hω hωb := by
    rw [commutatorElement_def, dgU_mul_cycU hω hωb]
    group
  have hcen := scU_mem_center hω hωb
  refine false_of_isType424_map_pair hT hQ ψ hker (dgU_pow_three hω hωb) (cycU_pow_three h)
    (by rw [hc]; exact (Subgroup.mem_center_iff.mp hcen _).symm)
    (by rw [hc]; exact (Subgroup.mem_center_iff.mp hcen _).symm)
    (su_not_mem_center_of_apply_ne h hq (i := 0) (j := 2) (by simpa [coe_dgU] using hω1))
    (su_mul_inv_zpow_not_mem_center h hq (dgU_pow_three hω hωb) fun m _ => ⟨1, 0, ?_, ?_⟩)
  · rw [coe_su_pow, coe_dgU, diagonal_pow, diagonal_apply_ne _ (by decide)]
  · simp [coe_cycU]

theorem false_of_isType424_su_three {X : Type} [Group X] [Finite X] (hT : Sec11.IsType424 X)
    (hQ : IsQuasisimple X) (hq : 2 < p ^ f) (h3 : (3 : K) = 0) {a : K} (ha0 : a ≠ 0)
    (ha : h.bar a = -a) (ψ : unitarySU p f K 3 →* X)
    (hker : ψ.ker ≤ Subgroup.center (unitarySU p f K 3)) : False := by
  have hxy : ⁅cycU h, tvU h3 ha⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (cycU_mul_tvU h3 ha)
  refine false_of_isType424_map_pair hT hQ ψ hker (cycU_pow_three h) (tvU_pow_three h3 ha)
    (by rw [hxy]; exact Commute.one_left _) (by rw [hxy]; exact Commute.one_left _)
    (su_not_mem_center_of_apply_ne_zero h hq (i := 1) (j := 0) (by decide) (by simp [coe_cycU]))
    (su_mul_inv_zpow_not_mem_center h hq (cycU_pow_three h) fun m hm => ?_)
  interval_cases m
  · exact ⟨0, 1, by simp, by simpa [coe_tvU] using ha0⟩
  · exact ⟨0, 1, by simp [coe_cycU], by simpa [coe_tvU] using ha0⟩
  · refine ⟨1, 0, ?_, by simpa [coe_tvU] using ha0⟩
    rw [coe_su_pow, coe_cycU]
    simp [pow_two, mul_apply, Fin.sum_univ_three]

theorem su3_mod_eq_one_of_isType424 (hU : UnitaryFieldData p f K) (hq : 2 < p ^ f) {X : Type}
    [Group X] [Finite X]
    (hT : Sec11.IsType424 X) (hQ : IsQuasisimple X) (ψ : unitarySU p f K 3 →* X)
    (hker : ψ.ker ≤ Subgroup.center (unitarySU p f K 3)) : p ^ f % 3 = 1 := by
  have := hU.finite
  have : CharP K p := hU.charP
  rcases (by omega : p ^ f % 3 = 0 ∨ p ^ f % 3 = 1 ∨ p ^ f % 3 = 2) with h0 | h1 | h2
  · exfalso
    have hp3 : p = 3 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hU.prime).mp
      (Nat.prime_three.dvd_of_dvd_pow (Nat.dvd_of_mod_eq_zero h0))).symm
    subst hp3
    have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
    obtain ⟨c, hc⟩ := hU.exists_bar_ne
    refine false_of_isType424_su_three (h := hU) hT hQ hq h3 (a := c - hU.bar c)
      (sub_ne_zero.mpr hc.symm) ?_ ψ hker
    rw [map_sub, UnitaryFieldData.bar_bar]
    ring
  · exact h1
  · exfalso
    have hK : Nat.card K % 3 = 1 := by
      rw [hU.card, pow_mul']
      rw [Nat.pow_mod, h2]
    obtain ⟨ω, hω, hω1⟩ := exists_cube_root_of_card_mod hK
    have hωb : hU.bar ω * ω = 1 := by
      rw [UnitaryFieldData.bar_apply]
      have e : p ^ f = 3 * (p ^ f / 3) + 2 := by omega
      rw [e, pow_add, pow_mul, hω, one_pow, one_mul, ← pow_succ, hω]
    exact false_of_isType424_su_two hT hQ hq hω hω1 hωb ψ hker

end CFSG.RankThree.PartTwo.Sec4.Item424Res3
