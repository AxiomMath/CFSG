module

public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411Tools
import CFSG.RankThree.PartTwo.KFacts.K72FieldKind
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearInvolution

public section

namespace CFSG.RankThree.PartTwo.Sec20

open Matrix CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open scoped MatrixGroups

variable {K : Type} [Field K]

@[expose] noncomputable def swapGL (l : Kˣ) : GL (Fin 2) K where
  val := !![0, (l : K); 1, 0]
  inv := !![0, 1; ((l⁻¹ : Kˣ) : K), 0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem coe_swapGL (l : Kˣ) :
    ((swapGL l : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![0, (l : K); 1, 0] := rfl

@[expose] noncomputable def diagFstGL (μ : Kˣ) : GL (Fin 2) K where
  val := !![(μ : K), 0; 0, 1]
  inv := !![((μ⁻¹ : Kˣ) : K), 0; 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem coe_diagFstGL (μ : Kˣ) :
    ((diagFstGL μ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![(μ : K), 0; 0, 1] := rfl

theorem coe_diagFstGL_inv (μ : Kˣ) :
    (((diagFstGL μ)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![((μ⁻¹ : Kˣ) : K), 0; 0, 1] := rfl

theorem swapGL_mul_sq (μ l : Kˣ) :
    swapGL (μ ^ 2 * l) = GeneralLinearGroup.scalar (Fin 2) μ *
      (diagFstGL μ * swapGL l * (diagFstGL μ)⁻¹) := by
  have hμ : (μ : K) ≠ 0 := μ.ne_zero
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_swapGL, coe_swapGL, coe_diagFstGL,
    coe_diagFstGL_inv, GeneralLinearGroup.coe_scalar]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply, sq, hμ, mul_assoc]

theorem exists_mul_swapGL_eq (G : GL (Fin 2) K) (l : Kˣ)
    (hG : G * G = GeneralLinearGroup.scalar (Fin 2) l)
    (hns : ¬ ((G : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧ (G : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
      (G : Matrix (Fin 2) (Fin 2) K) 0 0 = (G : Matrix (Fin 2) (Fin 2) K) 1 1)) :
    ∃ P : GL (Fin 2) K, G * P = P * swapGL l := by
  set A := (G : Matrix (Fin 2) (Fin 2) K) with hA
  have hAA : A * A = (l : K) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    have := congrArg (fun M : GL (Fin 2) K => (M : Matrix (Fin 2) (Fin 2) K)) hG
    simpa [GeneralLinearGroup.coe_scalar, Matrix.smul_one_eq_diagonal] using this
  have e : ∀ i j, (A * A) i j = ((l : K) • (1 : Matrix (Fin 2) (Fin 2) K)) i j := fun i j => by
    rw [hAA]
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0),
    smul_eq_mul, mul_one, mul_zero] at e00 e01 e10 e11
  have key : ∀ (B : Matrix (Fin 2) (Fin 2) K) (hB : B.det ≠ 0),
      A * B = B * !![0, (l : K); 1, 0] → ∃ P : GL (Fin 2) K, G * P = P * swapGL l := by
    intro B hB hAB
    exact ⟨GeneralLinearGroup.mkOfDetNeZero B hB, Units.ext hAB⟩
  by_cases hc : A 1 0 ≠ 0
  · refine key !![1, A 0 0; 0, A 1 0] (by simp [Matrix.det_fin_two, hc]) ?_
    rw [Matrix.eta_fin_two A]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | ring1 | linear_combination e00 | linear_combination e01 | linear_combination e10 |
        linear_combination e11
  · push Not at hc
    by_cases hb : A 0 1 ≠ 0
    · refine key !![0, A 0 1; 1, A 1 1] (by simp [Matrix.det_fin_two, hb]) ?_
      rw [Matrix.eta_fin_two A]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
        first | ring1 | linear_combination e00 | linear_combination e01 |
          linear_combination e10 | linear_combination e11
    · push Not at hb
      have had : A 0 0 ≠ A 1 1 := fun h => hns ⟨hb, hc, h⟩
      rw [hb, hc] at e00 e11
      refine key !![1, A 0 0; 1, A 1 1] (by
        simp only [Matrix.det_fin_two_of]
        intro h
        exact had (by linear_combination -h)) ?_
      rw [Matrix.eta_fin_two A, hb, hc]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
        first | ring1 | linear_combination e00 | linear_combination e11

theorem exists_eq_sq_or_eq_sq_mul [Finite K] (hK : ringChar K ≠ 2) (ν : Kˣ)
    (hν : ¬ IsSquare (ν : K)) (l : Kˣ) : ∃ μ : Kˣ, l = μ ^ 2 ∨ l = μ ^ 2 * ν := by
  have := Fintype.ofFinite K
  rcases FiniteField.pow_dichotomy hK l.ne_zero with h | h
  · obtain ⟨y, hy⟩ := (FiniteField.isSquare_iff hK l.ne_zero).mpr h
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact l.ne_zero (by simpa using hy)
    exact ⟨Units.mk0 y hy0, Or.inl (Units.ext (by simp [hy, sq]))⟩
  · have hν' : (ν : K) ^ (Fintype.card K / 2) = -1 := by
      rcases FiniteField.pow_dichotomy hK ν.ne_zero with h' | h'
      · exact absurd ((FiniteField.isSquare_iff hK ν.ne_zero).mpr h') hν
      · exact h'
    have hne : (l : K) * (ν : K)⁻¹ ≠ 0 := mul_ne_zero l.ne_zero (inv_ne_zero ν.ne_zero)
    obtain ⟨y, hy⟩ := (FiniteField.isSquare_iff hK hne).mpr (by
      rw [mul_pow, inv_pow, h, hν']
      norm_num)
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact hne (by simpa using hy)
    refine ⟨Units.mk0 y hy0, Or.inr (Units.ext ?_)⟩
    have hν0 : (ν : K) ≠ 0 := ν.ne_zero
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0]
    rw [sq, ← hy]
    field_simp

theorem exists_conj_swap_of_involution [Finite K] (hK : ringChar K ≠ 2) (ν : Kˣ)
    (hν : ¬ IsSquare (ν : K)) {g : PGL2 K} (hg : g * g = 1) (hg1 : g ≠ 1) :
    ∃ h : PGL2 K, h * g * h⁻¹ = ProjGenLinGroup.mk (swapGL 1) ∨
      h * g * h⁻¹ = ProjGenLinGroup.mk (swapGL ν) := by
  obtain ⟨G, rfl⟩ := ProjGenLinGroup.mk_surjective g
  have hGG : G * G ∈ Subgroup.center (GL (Fin 2) K) := by
    rw [← ProjGenLinGroup.mk_eq_one, map_mul]
    exact hg
  rw [GeneralLinearGroup.center_eq_range_scalar] at hGG
  obtain ⟨l, hl⟩ := hGG
  have hns : ¬ ((G : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧ (G : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
      (G : Matrix (Fin 2) (Fin 2) K) 0 0 = (G : Matrix (Fin 2) (Fin 2) K) 1 1) := by
    rintro ⟨hb, hc, had⟩
    apply hg1
    rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar]
    have hdet : (G : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := (Matrix.isUnit_iff_isUnit_det _).mp
      G.isUnit |>.ne_zero
    have h00 : (G : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := by
      intro h0
      apply hdet
      rw [Matrix.det_fin_two, hb, h0]
      ring
    refine ⟨Units.mk0 _ h00, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hb, hc, had, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  obtain ⟨P, hP⟩ := exists_mul_swapGL_eq G l hl.symm hns
  have hGP : G = P * swapGL l * P⁻¹ := by rw [← hP]; group
  obtain ⟨μ, hμ⟩ := exists_eq_sq_or_eq_sq_mul hK ν hν l
  have key : ∀ l₀ : Kˣ, l = μ ^ 2 * l₀ →
      (ProjGenLinGroup.mk (P * diagFstGL μ))⁻¹ * ProjGenLinGroup.mk G *
        (ProjGenLinGroup.mk (P * diagFstGL μ))⁻¹⁻¹ = ProjGenLinGroup.mk (swapGL l₀) := by
    intro l₀ hl₀
    rw [hGP, hl₀, swapGL_mul_sq μ l₀]
    simp only [map_mul, map_inv, ProjGenLinGroup.mk_scalar, one_mul]
    group
  rcases hμ with hl' | hl'
  · exact ⟨_, Or.inl (key 1 (by rw [hl', mul_one]))⟩
  · exact ⟨_, Or.inr (key ν hl')⟩

theorem ringEquiv_apply_eq_pow_of_orderOf_eq_two [Finite K] {p : ℕ} (hp : p.Prime)
    (hK : Nat.card K = p ^ 2) {σ : K ≃+* K} (hσ : orderOf σ = 2) (x : K) : σ x = x ^ p := by
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p 1 K :=
    ⟨hp, le_rfl, by rw [hK]⟩
  have hσσ : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
  rcases CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.ringEquiv_eq_refl_or_bar h hσσ with
    h1 | h1
  · rw [h1] at hσ
    exact absurd hσ (by rw [show RingEquiv.refl K = 1 from rfl, orderOf_one]; norm_num)
  · rw [h1 x, CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply, pow_one]

theorem exists_conj_normalForm_psl2 [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ 2) (ν : Kˣ) (hν : ¬ IsSquare (ν : K)) (α : MulAut (PSL2 K))
    (hα : orderOf α = 2) :
    ∃ β : MulAut (PSL2 K),
      β * α * β⁻¹ = pglAction K (ProjGenLinGroup.mk (swapGL 1)) ∨
      β * α * β⁻¹ = pglAction K (ProjGenLinGroup.mk (swapGL ν)) ∨
      ∃ σ : K ≃+* K, (∀ x, σ x = x ^ p) ∧ β * α * β⁻¹ = psl2FieldAut K σ := by
  have : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite K
  have hchar : CharP K p := charP_of_card_eq_prime_pow (f := 2)
    (by rw [← Nat.card_eq_fintype_card, hK])
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  by_cases hD : α ∈ (pglAction K).range
  · obtain ⟨g, rfl⟩ := hD
    have hg : g * g = 1 := by
      apply KFacts.pglAction_injective
      have h2 := pow_orderOf_eq_one (pglAction K g)
      rw [hα, sq] at h2
      rw [map_mul, map_one]
      exact h2
    have hg1 : g ≠ 1 := by
      rintro rfl
      rw [map_one, orderOf_one] at hα
      exact absurd hα (by norm_num)
    obtain ⟨h, hh⟩ := exists_conj_swap_of_involution hK2 ν hν hg hg1
    refine ⟨pglAction K h, ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    rcases hh with hh | hh
    · exact Or.inl (by rw [hh])
    · exact Or.inr (Or.inl (by rw [hh]))
  · obtain ⟨σ, hσ, g, hαg⟩ :=
      KFacts.linear_two_prime_order_field_descent Nat.prime_two α hα hD
    refine ⟨(pglAction K g)⁻¹, Or.inr (Or.inr ⟨σ, ringEquiv_apply_eq_pow_of_orderOf_eq_two hp hK hσ,
      ?_⟩)⟩
    rw [hαg]
    group

theorem exists_dvd_orderOf_word1411 [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ 2) (ν : Kˣ) (hν : ¬ IsSquare (ν : K)) {r : ℕ}
    (h0 : ∃ x₁ x₂ x₃ : PSL2 K,
      r ∣ orderOf (word1411 (pglAction K (ProjGenLinGroup.mk (swapGL 1))) x₁ x₂ x₃))
    (h1 : ∃ x₁ x₂ x₃ : PSL2 K,
      r ∣ orderOf (word1411 (pglAction K (ProjGenLinGroup.mk (swapGL ν))) x₁ x₂ x₃))
    (h2 : ∀ σ : K ≃+* K, (∀ x, σ x = x ^ p) →
      ∃ x₁ x₂ x₃ : PSL2 K, r ∣ orderOf (word1411 (psl2FieldAut K σ) x₁ x₂ x₃))
    (α : MulAut (PSL2 K)) (hα : orderOf α = 2) :
    ∃ x₁ x₂ x₃ : PSL2 K, r ∣ orderOf (word1411 α x₁ x₂ x₃) := by
  obtain ⟨β, hβ⟩ := exists_conj_normalForm_psl2 hp hp2 hK ν hν α hα
  have key : ∀ α₀ : MulAut (PSL2 K), β * α * β⁻¹ = α₀ →
      (∃ x₁ x₂ x₃ : PSL2 K, r ∣ orderOf (word1411 α₀ x₁ x₂ x₃)) →
      ∃ x₁ x₂ x₃ : PSL2 K, r ∣ orderOf (word1411 α x₁ x₂ x₃) := by
    rintro α₀ rfl ⟨y₁, y₂, y₃, hy⟩
    refine ⟨β⁻¹ y₁, β⁻¹ y₂, β⁻¹ y₃, ?_⟩
    have e : word1411 α (β⁻¹ y₁) (β⁻¹ y₂) (β⁻¹ y₃) = β⁻¹ (word1411 (β * α * β⁻¹) y₁ y₂ y₃) := by
      have h := word1411_conj β⁻¹ (β * α * β⁻¹) y₁ y₂ y₃
      rw [show β⁻¹ * (β * α * β⁻¹) * β⁻¹⁻¹ = α by group] at h
      exact h
    rw [e, MulEquiv.orderOf_eq]
    exact hy
  rcases hβ with hβ | hβ | ⟨σ, hσ, hβ⟩
  · exact key _ hβ h0
  · exact key _ hβ h1
  · exact key _ hβ (h2 σ hσ)

end CFSG.RankThree.PartTwo.Sec20
