module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec9Tensor

public section

namespace CFSG.RankThree.GF2n.Stroth80.HS9

open CFSG CFSG.Open CFSG.Open.StatedAPI
open Matrix
open CFSG.Quasithin.G11.P3Ortho.Om4 CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit

section Algebra

variable {K : Type} [Field K]

theorem exists_smul_of_vecMulVec_eq95 {a b a' b' : Fin 2 → K} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : Matrix.vecMulVec a b = Matrix.vecMulVec a' b') :
    ∃ μ : K, μ ≠ 0 ∧ a' = μ • a ∧ b' = μ⁻¹ • b := by
  have hent : ∀ i j, a i * b j = a' i * b' j := fun i j => by
    have := congrFun (congrFun h i) j
    simpa [Matrix.vecMulVec_apply] using this
  obtain ⟨i₀, hi₀⟩ : ∃ i, a i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact ha (funext hcon)
  obtain ⟨j₀, hj₀⟩ : ∃ j, b j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hb (funext hcon)
  have hb'j₀ : b' j₀ ≠ 0 := by
    intro h0
    have := hent i₀ j₀
    rw [h0, mul_zero] at this
    exact mul_ne_zero hi₀ hj₀ this
  set μ : K := b j₀ / b' j₀ with hμ
  have hμ0 : μ ≠ 0 := div_ne_zero hj₀ hb'j₀
  refine ⟨μ, hμ0, ?_, ?_⟩
  · funext i
    have := hent i j₀
    simp only [Pi.smul_apply, smul_eq_mul, hμ]
    field_simp
    linear_combination -this
  · funext j
    have h1 : a' i₀ = μ * a i₀ := by
      have := hent i₀ j₀
      simp only [hμ]
      field_simp
      linear_combination -this
    have := hent i₀ j
    rw [h1] at this
    simp only [Pi.smul_apply, smul_eq_mul]
    have h2 : μ * (a i₀ * b' j) = a i₀ * b j := by linear_combination -this
    have h3 : a i₀ * (μ * b' j - b j) = 0 := by linear_combination h2
    have h4 : μ * b' j = b j := sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_left hi₀)
    rw [← h4, ← mul_assoc, inv_mul_cancel₀ hμ0, one_mul]

theorem sl2_eq_one_of_fixed95 [CharP K 2] (A : Matrix.SpecialLinearGroup (Fin 2) K)
    {a : Fin 2 → K} (ha : a ≠ 0) (hAa : (A : Matrix (Fin 2) (Fin 2) K) *ᵥ a = a)
    {m : ℕ} (hm : Odd m) (hAm : A ^ m = 1) : A = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set M : Matrix (Fin 2) (Fin 2) K := (A : Matrix (Fin 2) (Fin 2) K) with hMdef
  have hdet : M.det = 1 := A.2
  obtain ⟨p, q, r, s, hM⟩ : ∃ p q r s : K, M = !![p, q; r, s] :=
    ⟨M 0 0, M 0 1, M 1 0, M 1 1, Matrix.eta_fin_two M⟩
  rw [hM, Matrix.det_fin_two_of] at hdet
  have e0 := congrFun hAa 0
  have e1 := congrFun hAa 1
  rw [hM] at e0 e1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at e0 e1
  have hbr : (p - 1) * (s - 1) - q * r = 0 := by
    by_cases ha0 : a 0 = 0
    · have ha1 : a 1 ≠ 0 := fun h => ha (funext fun i => by fin_cases i <;> simp [ha0, h])
      have : ((p - 1) * (s - 1) - q * r) * a 1 = 0 := by
        linear_combination (-(r)) * e0 + (p - 1) * e1
      exact (mul_eq_zero.mp this).resolve_right ha1
    · have : ((p - 1) * (s - 1) - q * r) * a 0 = 0 := by
        linear_combination (s - 1) * e0 - q * e1
      exact (mul_eq_zero.mp this).resolve_right ha0
  have hps : p + s = 0 := by linear_combination -hbr + hdet + h2
  have hAA : M * M = 1 := by
    rw [hM, Matrix.mul_fin_two, Matrix.one_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    · linear_combination (-1 : K) * hdet + p * hps + (-1 : K) * h2 + (0 : K) * hbr
    · linear_combination q * hps
    · linear_combination r * hps
    · linear_combination (-1 : K) * hdet + s * hps + (-1 : K) * h2
  have hA2 : A ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using hAA)
  obtain ⟨k, rfl⟩ := hm
  have : A ^ (2 * k + 1) = A := by rw [pow_succ, pow_mul, hA2, one_pow, one_mul]
  rw [← this]
  exact hAm

theorem sl2_transpose_pow95 (A : Matrix.SpecialLinearGroup (Fin 2) K) (m : ℕ) :
    (A ^ m).transpose = (A.transpose) ^ m := by
  apply Subtype.ext
  simp [Matrix.SpecialLinearGroup.coe_transpose, Matrix.SpecialLinearGroup.coe_pow,
    Matrix.transpose_pow]

theorem mulVec_pow_eq_smul95 {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n K)
    {v : n → K} {μ : K} (h : M *ᵥ v = μ • v) (k : ℕ) : (M ^ k) *ᵥ v = μ ^ k • v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ]
    ring_nf

end Algebra

section Omega

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem eq_one_of_fix_singular95 (h4 : 4 ≤ Nat.card K) {g : GL (Fin 2 ⊕ Fin 2) K}
    (hg : g ∈ StatedOmega (StatedQuadPlus 2 K)) {m : ℕ} (hm : Odd m) (hgm : g ^ m = 1)
    (hmK : ∀ a : K, a ^ m = 1 → a = 1) {p : Fin 2 ⊕ Fin 2 → K} (hp0 : p ≠ 0)
    (hpQ : StatedQuadPlus 2 K p = 0)
    (hgp : (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ p = p) : g = 1 := by
  classical
  have h1 : Ψ K g ∈ (StatedOmega (StatedQuadPlus 2 K)).map (Ψ K).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hg
  rw [map_statedOmega, commutator_eq_range h4] at h1
  obtain ⟨z, hz⟩ := h1
  have hzX : ∀ X : Matrix (Fin 2) (Fin 2) K,
      rho' K z X = (z.1 : Matrix (Fin 2) (Fin 2) K) * X *
        ((z.2⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) :=
    fun X => specialRho_apply z X
  set M₀ : Matrix (Fin 2) (Fin 2) K := toMat K p with hM₀
  have hdet : M₀.det = 0 := by rw [hM₀, det_toMat, hpQ]
  have hM0 : M₀ ≠ 0 := by
    intro h
    exact hp0 ((toMat K).injective (by rw [← hM₀, h, map_zero]))
  have hfix : (z.1 : Matrix (Fin 2) (Fin 2) K) * M₀ *
      ((z.2⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = M₀ := by
    rw [← hzX, hz]
    have : Ψ K g M₀ = toMat K ((g : Matrix _ _ K) *ᵥ (toMat K).symm M₀) := Ψ_apply K g M₀
    rw [this, hM₀, LinearEquiv.symm_apply_apply, hgp]
  obtain ⟨a, b, ha, hb, hab⟩ := exists_vecMulVec_of_det_eq_zero hdet hM0
  rw [hab, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul] at hfix
  obtain ⟨μ, hμ0, hμa, hμb⟩ := exists_smul_of_vecMulVec_eq95 ha hb hfix.symm
  have hzm : z ^ m = 1 := by
    apply rho'_injective (K := K)
    rw [map_pow, hz, map_one, ← map_pow, hgm, map_one]
  have hA : z.1 ^ m = 1 := by
    have := congrArg Prod.fst hzm
    simpa using this
  have hB : z.2 ^ m = 1 := by
    have := congrArg Prod.snd hzm
    simpa using this
  have hμ1 : μ = 1 := by
    apply hmK
    have h := mulVec_pow_eq_smul95 (z.1 : Matrix (Fin 2) (Fin 2) K) (v := a) (μ := μ) hμa m
    have hpowA : ((z.1 : Matrix (Fin 2) (Fin 2) K) ^ m) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_pow, hA]; rfl
    rw [hpowA, Matrix.one_mulVec] at h
    obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact ha (funext hcon)
    have := congrFun h i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    have h3 : (μ ^ m - 1) * a i = 0 := by linear_combination -this
    exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right hi)
  subst hμ1
  have hAa : (z.1 : Matrix (Fin 2) (Fin 2) K) *ᵥ a = a := by simpa using hμa
  have hz1 : z.1 = 1 := sl2_eq_one_of_fixed95 z.1 ha hAa hm hA
  have hbB : (z.2⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K).transpose.val *ᵥ b = b := by
    rw [Matrix.SpecialLinearGroup.coe_transpose, Matrix.mulVec_transpose]
    simpa using hμb
  have hBm : ((z.2⁻¹).transpose) ^ m = 1 := by
    rw [← sl2_transpose_pow95, inv_pow, hB, inv_one]
    apply Subtype.ext
    simp
  have hz2' : (z.2⁻¹).transpose = 1 := sl2_eq_one_of_fixed95 _ hb hbB hm hBm
  have hz2 : z.2 = 1 := by
    have h5 : z.2⁻¹ = 1 := by
      apply Subtype.ext
      have := congrArg Subtype.val hz2'
      simpa [Matrix.SpecialLinearGroup.coe_transpose] using this
    simpa using h5
  have hz11 : z = 1 := Prod.ext hz1 hz2
  rw [hz11, map_one] at hz
  exact (Ψ K).injective (by rw [← hz, map_one])

end Omega

end CFSG.RankThree.GF2n.Stroth80.HS9
