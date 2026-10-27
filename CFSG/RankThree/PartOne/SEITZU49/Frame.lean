module

public import CFSG.RankThree.PartOne.CTP.SeitzU5Eigen

public section

namespace CFSG.RankThree.PartOne.SEITZU49.Frame

open Matrix CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.RankThree.PartOne.CTP.U5Eigen (IsIsom isIsom_of_conjTr herm_eq_zero_of_eigen pow_mul_comm
  pow_inj exists_eigen shiftMat shiftMat_apply)

variable {K : Type} [Field K] (σ : K ≃+* K)

@[expose] def shiftZ (z : K) : Matrix (Fin 5) (Fin 5) K :=
  shiftMat * Matrix.diagonal ![1, 1, 1, 1, z]

theorem conjTr_pow_mul_pow {F : Matrix (Fin 5) (Fin 5) K} (hF : conjTr σ F * F = 1) (k : ℕ) :
    conjTr σ (F ^ k) * F ^ k = 1 := by
  induction k with
  | zero => simp [conjTr_one]
  | succ k ih =>
    rw [pow_succ', conjTr_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (conjTr σ F), hF,
      Matrix.one_mul, ih]

theorem exists_frame_z (hσ : IsUnitaryInvolution σ) (h2 : (2 : K) = 0)
    (hnorm5 : ∀ x : K, x ^ 5 = 1 → σ x * x = 1)
    {ζ : K} (hζ5 : ζ ^ 5 = 1) (hζ1 : ζ ≠ 1)
    {E F : Matrix (Fin 5) (Fin 5) K} (hEc : conjTr σ E * E = 1) (hFc : conjTr σ F * F = 1)
    (hE5 : E ^ 5 = 1) {z : K} (hF5 : F ^ 5 = z • (1 : Matrix (Fin 5) (Fin 5) K))
    (hEF : E * F = ζ • (F * E)) :
    ∃ (P : Matrix (Fin 5) (Fin 5) K) (lam : K), conjTr σ P * P = 1 ∧ lam ^ 5 = 1 ∧
      E * P = P * Matrix.diagonal (fun j : Fin 5 => lam * ζ ^ (j : ℕ)) ∧
        F * P = P * shiftZ z := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hE : IsIsom σ E := isIsom_of_conjTr σ hEc
  have hord : orderOf ζ = 5 := orderOf_eq_prime hζ5 hζ1
  have hne : ∀ k : ℕ, 0 < k → k < 5 → ζ ^ k ≠ 1 := fun k hk hk5 =>
    pow_ne_one_of_lt_orderOf (by omega) (by rw [hord]; exact hk5)
  have hz0 : ζ ≠ 0 := by rintro rfl; simp at hζ5
  obtain ⟨j, u, hj, hν, hEu⟩ := exists_eigen σ h2 hnorm5 hζ5 hζ1 hE hE5
  set ν := herm σ u u with hνdef
  have hνfix : σ ν = ν := herm_self_fixed σ hσ.invol u
  have hνinv : σ ν⁻¹ = ν⁻¹ := by rw [map_inv₀, hνfix]
  obtain ⟨c', hc'⟩ := hσ.exists_norm hνinv
  set v₀ : Fin 5 → K := c' • u with hv₀
  have hv₀n : herm σ v₀ v₀ = 1 := by
    rw [hv₀, herm_smul_left, herm_smul_right]
    calc σ c' * (c' * ν) = (σ c' * c') * ν := by ring
      _ = 1 := by rw [hc']; exact inv_mul_cancel₀ hν
  have hEv₀ : E *ᵥ v₀ = ζ ^ j • v₀ := by
    rw [hv₀, Matrix.mulVec_smul, hEu, smul_smul, smul_smul, mul_comm]
  set lam : K := ζ ^ j with hlam
  have hlam5 : lam ^ 5 = 1 := by
    rw [hlam, ← pow_mul, mul_comm, pow_mul, hζ5, one_pow]
  set vcol : ℕ → (Fin 5 → K) := fun k => F ^ k *ᵥ v₀ with hvcol
  have hEv : ∀ k : ℕ, E *ᵥ vcol k = (lam * ζ ^ k) • vcol k := by
    intro k
    simp only [hvcol]
    rw [Matrix.mulVec_mulVec, pow_mul_comm hEF, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
      hEv₀, Matrix.mulVec_smul, smul_smul, mul_comm]
  have hFv : ∀ k : ℕ, F *ᵥ vcol k = vcol (k + 1) := by
    intro k
    simp only [hvcol]
    rw [Matrix.mulVec_mulVec, ← pow_succ']
  have hv5 : vcol 5 = z • vcol 0 := by simp [hvcol, hF5, Matrix.smul_mulVec]
  have hvn : ∀ k : ℕ, herm σ (vcol k) (vcol k) = 1 := fun k => by
    simp only [hvcol]
    rw [herm_mulVec, conjTr_pow_mul_pow σ hFc k, Matrix.one_mulVec, hv₀n]
  have hnorm : ∀ k : ℕ, σ (lam * ζ ^ k) * (lam * ζ ^ k) = 1 := fun k =>
    hnorm5 _ (by rw [mul_pow, hlam5, ← pow_mul, mul_comm k 5, pow_mul, hζ5, one_pow, one_mul])
  have hvo : ∀ i k : ℕ, i < 5 → k < 5 → i ≠ k → herm σ (vcol i) (vcol k) = 0 := by
    intro i k hi hk hik
    refine herm_eq_zero_of_eigen σ hE (hEv i) (hEv k) ?_
    intro h1
    have hli : lam * ζ ^ i ≠ 0 := mul_ne_zero (pow_ne_zero _ hz0) (pow_ne_zero _ hz0)
    have hσi : σ (lam * ζ ^ i) = (lam * ζ ^ i)⁻¹ := eq_inv_of_mul_eq_one_left (hnorm i)
    rw [hσi] at h1
    have h1' : lam * ζ ^ i = lam * ζ ^ k := by
      have e : lam * ζ ^ k = (lam * ζ ^ i) * ((lam * ζ ^ i)⁻¹ * (lam * ζ ^ k)) := by field_simp
      rw [e, h1, mul_one]
    exact hik (pow_inj hζ5 hζ1 hi hk (mul_left_cancel₀ (pow_ne_zero _ hz0) h1'))
  refine ⟨Matrix.of fun r k => vcol (k : ℕ) r, lam, ?_, hlam5, ?_, ?_⟩
  · ext i k
    simp only [conjTr, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
      Matrix.of_apply, Matrix.one_apply]
    show herm σ (vcol i) (vcol k) = _
    by_cases hik : i = k
    · subst hik; simp [hvn]
    · simp only [hik, ite_false]; exact hvo i k i.2 k.2 (fun h => hik (Fin.ext h))
  · ext r k
    rw [Matrix.mul_diagonal]
    have := congrFun (hEv k) r
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, mul_comm] using this
  · ext r k
    have hFv' : ∀ k : Fin 5, F *ᵥ vcol (k : ℕ) =
        (![1, 1, 1, 1, z] k) • vcol ((k + 1 : Fin 5) : ℕ) := by
      intro k
      fin_cases k
      · simpa using hFv 0
      · simpa using hFv 1
      · simpa using hFv 2
      · simpa using hFv 3
      · exact (hFv 4).trans (by rw [show (4 : ℕ) + 1 = 5 from rfl, hv5]; rfl)
    have hS : ∀ s k : Fin 5, (shiftZ z : Matrix (Fin 5) (Fin 5) K) s k =
        if k = s - 1 then ![1, 1, 1, 1, z] k else 0 := by
      intro s k
      rw [shiftZ, Matrix.mul_diagonal, shiftMat_apply]
      split_ifs <;> simp
    have h1 := congrFun (hFv' k) r
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h1
    rw [Matrix.mul_apply, Matrix.mul_apply]
    simp only [Matrix.of_apply, hS]
    rw [h1, Finset.sum_eq_single (k + 1)]
    · simp [mul_comm]
    · intro s _ hs
      have : ¬ k = s - 1 := by
        intro h
        apply hs
        rw [h]; simp
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h


end CFSG.RankThree.PartOne.SEITZU49.Frame
