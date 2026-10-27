module

public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411L2GenTorus
import CFSG.RankThree.PartTwo.KFacts.AutPSL2OrderThree
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoPglFaithful
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearInvolution

public section

namespace CFSG.RankThree.PartTwo.Sec20

open Matrix CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem eq_pglAction_or_eq_conj_psl2FieldAut [Finite K] (α : MulAut (PSL2 K))
    (hα : orderOf α = 2) :
    (∃ g : PGL2 K, g ≠ 1 ∧ g * g = 1 ∧ α = pglAction K g) ∨
      ∃ σ : K ≃+* K, orderOf σ = 2 ∧ ∃ β : MulAut (PSL2 K), α = β * psl2FieldAut K σ * β⁻¹ := by
  by_cases hD : α ∈ (pglAction K).range
  · obtain ⟨g, rfl⟩ := hD
    refine Or.inl ⟨g, ?_, ?_, rfl⟩
    · rintro rfl
      rw [map_one, orderOf_one] at hα
      exact absurd hα (by norm_num)
    · apply pglAction_injective K
      have h2 := pow_orderOf_eq_one (pglAction K g)
      rw [hα, sq] at h2
      rw [map_mul, map_one]
      exact h2
  · obtain ⟨σ, hσ, g, hαg⟩ := KFacts.linear_two_prime_order_field_descent Nat.prime_two α hα hD
    exact Or.inr ⟨σ, hσ, pglAction K g, hαg⟩

theorem exists_eq_two_mul_of_orderOf_ringEquiv_eq_two [Finite K] {p f : ℕ} (hp : p.Prime)
    (hK : Nat.card K = p ^ f) {σ : K ≃+* K} (hσ : orderOf σ = 2) :
    ∃ m : ℕ, 1 ≤ m ∧ f = 2 * m ∧ ∀ x, σ x = x ^ p ^ m := by
  obtain ⟨hcard, -⟩ := CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hp K hK
  have h2 : 2 ∣ f := by
    rw [← hσ, ← hcard]
    exact orderOf_dvd_natCard σ
  obtain ⟨m, rfl⟩ := h2
  have hm : 1 ≤ m := by
    by_contra h0
    obtain rfl : m = 0 := by omega
    have h1 := Finite.one_lt_card (α := K)
    rw [hK, mul_zero, pow_zero] at h1
    exact lt_irrefl 1 h1
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p m K := ⟨hp, hm, hK⟩
  have hσσ : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
  refine ⟨m, hm, rfl, fun x => ?_⟩
  rcases CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.ringEquiv_eq_refl_or_bar h hσσ with
    h1 | h1
  · rw [h1] at hσ
    exact absurd hσ (by rw [show RingEquiv.refl K = 1 from rfl, orderOf_one]; norm_num)
  · rw [h1 x, CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply]

theorem exists_not_isSquare_sq_ne_one [Finite K] (hK2 : ringChar K ≠ 2) (h15 : (15 : K) ≠ 0) :
    ∃ ν : Kˣ, ¬ IsSquare (ν : K) ∧ (ν : K) ^ 2 ≠ 1 := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK2
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare hK2
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact ha ⟨0, by ring⟩
  by_cases h1 : a ^ 2 = 1
  · have ha1 : a = -1 := by
      have : (a - 1) * (a + 1) = 0 := by linear_combination h1
      rcases mul_eq_zero.mp this with h | h
      · exact absurd ⟨1, by linear_combination h⟩ ha
      · linear_combination h
    refine ⟨Units.mk0 (4 * a) (mul_ne_zero h4 ha0), ?_, ?_⟩
    · rintro ⟨r, hr⟩
      apply ha
      refine ⟨r / 2, ?_⟩
      simp only [Units.val_mk0] at hr
      rw [div_mul_div_comm, show (2 : K) * 2 = 4 by norm_num, ← hr, mul_div_cancel_left₀ a h4]
    · simp only [Units.val_mk0]
      rw [ha1]
      intro h
      exact h15 (by linear_combination h)
  · exact ⟨Units.mk0 a ha0, ha, h1⟩

theorem excl1411_pglAction_swapGL_one {p : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    (hp105 : ¬ p ∣ 105) : Excl1411 (pglAction K (ProjGenLinGroup.mk (swapGL (1 : Kˣ)))) := by
  have h2 : (2 : K) ≠ 0 := by
    intro h0
    have := (CharP.cast_eq_zero_iff K p 2).mp (by exact_mod_cast h0)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp this)
  have hdet : (!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
    rw [Matrix.det_fin_two_of]
    intro h
    exact h2 (by linear_combination -h)
  set P := GeneralLinearGroup.mkOfDetNeZero _ hdet with hP
  have hPD : swapGL (1 : Kˣ) = P * negDiagGL * P⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_swapGL, coe_negDiagGL]
    change !![0, ((1 : Kˣ) : K); 1, 0] * !![1, 1; 1, -1] = !![1, 1; 1, -1] * !![1, 0; 0, -1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  obtain ⟨x, hx⟩ := exists_unipotent_dvd_orderOf (K := K) hp2
  rw [hPD]
  simp only [map_mul, map_inv]
  exact (excl1411_of_odd_not_dvd_105 ((Fact.out : p.Prime).odd_of_ne_two hp2) hp105 hx).conj _

theorem word1411_pglAction_mk_mk (G : GL (Fin 2) K) (X₁ X₂ X₃ Y₁ Y₂ : SL(2, K))
    (h₁ : (G : Matrix (Fin 2) (Fin 2) K) * (X₁ : Matrix (Fin 2) (Fin 2) K) =
      (Y₁ : Matrix (Fin 2) (Fin 2) K) * G)
    (h₂ : (G : Matrix (Fin 2) (Fin 2) K) * ((X₂⁻¹ * X₃ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      (Y₂ : Matrix (Fin 2) (Fin 2) K) * G) :
    word1411 (pglAction K (ProjGenLinGroup.mk G)) (QuotientGroup.mk X₁ : PSL2 K)
      (QuotientGroup.mk X₂) (QuotientGroup.mk X₃) =
      QuotientGroup.mk (Y₁ * X₁⁻¹ * (X₂ * Y₂ * X₃⁻¹)) := by
  have e₂ : (QuotientGroup.mk X₂ : PSL2 K)⁻¹ * QuotientGroup.mk X₃ =
      QuotientGroup.mk (X₂⁻¹ * X₃) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  unfold word1411
  rw [e₂, pglAction_mk_mk G X₁ Y₁ h₁, pglAction_mk_mk G _ Y₂ h₂]
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]

private def swX₁ : SL(2, K) := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two_of]⟩

private def swX₂ : SL(2, K) := ⟨!![1, 1; -1, 0], by simp [Matrix.det_fin_two_of]⟩

private def swY₁ (ν : Kˣ) : SL(2, K) :=
  ⟨!![0, -(ν : K); ((ν⁻¹ : Kˣ) : K), 0], by simp [Matrix.det_fin_two_of]⟩

private def swY₂ (ν : Kˣ) : SL(2, K) :=
  ⟨!![0, (ν : K); -((ν⁻¹ : Kˣ) : K), 0], by simp [Matrix.det_fin_two_of]⟩

private theorem word1411_pglAction_swapGL (ν : Kˣ) :
    word1411 (pglAction K (ProjGenLinGroup.mk (swapGL ν))) (QuotientGroup.mk swX₁ : PSL2 K)
      (QuotientGroup.mk swX₂) (QuotientGroup.mk (unipSL (-1))) =
      QuotientGroup.mk (unipSL (1 - (ν : K) ^ 2)) := by
  have hu : (ν : K) * ((ν⁻¹ : Kˣ) : K) = 1 := Units.mul_inv ν
  have hu' : (ν : K) * (ν : K)⁻¹ = 1 := mul_inv_cancel₀ ν.ne_zero
  rw [word1411_pglAction_mk_mk (swapGL ν) swX₁ swX₂ (unipSL (-1)) (swY₁ ν) (swY₂ ν) ?_ ?_]
  · congr 1
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv]
    change !![0, -(ν : K); ((ν⁻¹ : Kˣ) : K), 0] * adjugate !![0, 1; -1, 0] *
      (!![1, 1; -1, 0] * !![0, (ν : K); -((ν⁻¹ : Kˣ) : K), 0] * adjugate !![1, -1; 0, 1]) =
      !![1, 1 - (ν : K) ^ 2; 0, 1]
    rw [Matrix.adjugate_fin_two_of, Matrix.adjugate_fin_two_of]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind
  · rw [coe_swapGL]
    change !![0, (ν : K); 1, 0] * !![0, 1; -1, 0] =
      !![0, -(ν : K); ((ν⁻¹ : Kˣ) : K), 0] * !![0, (ν : K); 1, 0]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind
  · rw [coe_swapGL]
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv]
    change !![0, (ν : K); 1, 0] * (adjugate !![1, 1; -1, 0] * !![1, -1; 0, 1]) =
      !![0, (ν : K); -((ν⁻¹ : Kˣ) : K), 0] * !![0, (ν : K); 1, 0]
    rw [Matrix.adjugate_fin_two_of]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind

theorem exists_word1411_pglAction_swapGL_dvd {p : ℕ} [Fact p.Prime] [CharP K p] (ν : Kˣ)
    (hν : (ν : K) ^ 2 ≠ 1) :
    ∃ x₁ x₂ x₃ : PSL2 K,
      p ∣ orderOf (word1411 (pglAction K (ProjGenLinGroup.mk (swapGL ν))) x₁ x₂ x₃) := by
  refine ⟨QuotientGroup.mk swX₁, QuotientGroup.mk swX₂, QuotientGroup.mk (unipSL (-1)), ?_⟩
  rw [word1411_pglAction_swapGL]
  exact dvd_of_eq (orderOf_mk_unipSL (sub_ne_zero.mpr (Ne.symm hν))).symm

theorem orderOf_mk_eq_prime_pow {N : SL(2, K)} {r k : ℕ} (hr : r.Prime)
    (hN : (N : Matrix (Fin 2) (Fin 2) K) ^ r ^ (k + 1) = -1 ∨
      (N : Matrix (Fin 2) (Fin 2) K) ^ r ^ (k + 1) = 1)
    (h01 : ((N : Matrix (Fin 2) (Fin 2) K) ^ r ^ k) 0 1 ≠ 0) :
    orderOf (QuotientGroup.mk N : PSL2 K) = r ^ (k + 1) := by
  have : Fact r.Prime := ⟨hr⟩
  refine orderOf_eq_prime_pow (fun h1 => h01 ?_) ?_
  · rw [← Matrix.SpecialLinearGroup.coe_pow]
    exact coe_apply_zero_one_eq_zero_of_mem_center
      ((QuotientGroup.eq_one_iff _).mp (by rw [QuotientGroup.mk_pow]; exact h1))
  · rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact mem_center_of_coe_eq_neg_one_or_one (by rwa [Matrix.SpecialLinearGroup.coe_pow])

private def q31X : SL(2, K) := ⟨!![-3, 4; -1, 1], by rw [Matrix.det_fin_two_of]; norm_num⟩

private def q31Y : SL(2, K) := ⟨!![1, 1; -4, -3], by rw [Matrix.det_fin_two_of]; norm_num⟩

private theorem q31_pow (h31 : (31 : K) = 0) :
    (!![2, -7; -7, 25] : Matrix (Fin 2) (Fin 2) K) ^ 16 = -1 ∧
      ((!![2, -7; -7, 25] : Matrix (Fin 2) (Fin 2) K) ^ 8) 0 1 = 5 := by
  have e2 : (!![2, -7; -7, 25] : Matrix (Fin 2) (Fin 2) K) ^ 2 = !![-9, -3; -3, -8] := by
    rw [sq]; ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind
  have e4 : (!![2, -7; -7, 25] : Matrix (Fin 2) (Fin 2) K) ^ 4 = !![-3, -11; -11, 11] := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, e2, sq]; ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind
  have e8 : (!![2, -7; -7, 25] : Matrix (Fin 2) (Fin 2) K) ^ 8 = !![6, 5; 5, -6] := by
    rw [show 8 = 4 * 2 from rfl, pow_mul, e4, sq]; ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind
  refine ⟨?_, by rw [e8]; rfl⟩
  rw [show 16 = 8 * 2 from rfl, pow_mul, e8, sq]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> grind

theorem exists_sixteen_dvd_orderOf_L2_31 (h31 : (31 : K) = 0) :
    ∃ x : PSL2 K, 16 ∣ orderOf (pglAction K (ProjGenLinGroup.mk (swapGL (-1 : Kˣ))) x * x⁻¹) := by
  have h5 : (5 : K) ≠ 0 := fun h => one_ne_zero (α := K) (by linear_combination h31 - 6 * h)
  refine ⟨QuotientGroup.mk q31X, dvd_of_eq ?_⟩
  have hα := pglAction_mk_mk (swapGL (-1 : Kˣ)) q31X q31Y (by
    rw [coe_swapGL]
    change !![0, ((-1 : Kˣ) : K); 1, 0] * !![-3, 4; -1, 1] =
      !![1, 1; -4, -3] * !![0, ((-1 : Kˣ) : K); 1, 0]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two])
  have hW : ((q31Y * q31X⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![2, -7; -7, 25] := by
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv]
    change !![1, 1; -4, -3] * adjugate !![-3, 4; -1, 1] = _
    rw [Matrix.adjugate_fin_two_of]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  obtain ⟨h16, h8⟩ := q31_pow h31
  rw [hα, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    orderOf_mk_eq_prime_pow (k := 3) Nat.prime_two
      (Or.inl (by rw [hW, show (2 : ℕ) ^ (3 + 1) = 16 by norm_num]; exact h16))
      (by rw [hW, show (2 : ℕ) ^ 3 = 8 by norm_num, h8]; exact h5)]
  norm_num

end CFSG.RankThree.PartTwo.Sec20
