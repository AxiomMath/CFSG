module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTailEich

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix

namespace OrthRestTail

variable {K : Type} [Field K]

@[expose] def binF (b c : K) (x : Fin 2 → K) : K := x 0 ^ 2 + b * x 0 * x 1 + c * x 1 ^ 2

section Mul

variable {b c : K}

@[expose] def mulMat (z : QuadraticAlgebra K c b) : Matrix (Fin 2) (Fin 2) K :=
  !![z.re, c * z.im; z.im, z.re + b * z.im]

theorem mulMat_mul (z w : QuadraticAlgebra K c b) : mulMat (z * w) = mulMat z * mulMat w := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mulMat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem mulMat_one : mulMat (1 : QuadraticAlgebra K c b) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mulMat, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

@[expose] def mulMatHom : QuadraticAlgebra K c b →* Matrix (Fin 2) (Fin 2) K where
  toFun := mulMat
  map_one' := mulMat_one
  map_mul' := mulMat_mul

theorem det_mulMat (z : QuadraticAlgebra K c b) : (mulMat z).det = z.norm := by
  rw [mulMat, Matrix.det_fin_two_of, QuadraticAlgebra.norm_def]
  ring

@[expose] def starMat (b : K) : Matrix (Fin 2) (Fin 2) K := !![1, b; 0, -1]

theorem starMat_mul_mulMat (z : QuadraticAlgebra K c b) :
    starMat b * mulMat z = mulMat (star z) * starMat b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [starMat, mulMat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem mulMat_mulVec (z : QuadraticAlgebra K c b) (x : Fin 2 → K) :
    (⟨(mulMat z *ᵥ x) 0, (mulMat z *ᵥ x) 1⟩ : QuadraticAlgebra K c b) = z * ⟨x 0, x 1⟩ := by
  (ext <;> simp [mulMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]); ring

theorem starMat_mulVec (x : Fin 2 → K) :
    (⟨(starMat b *ᵥ x) 0, (starMat b *ᵥ x) 1⟩ : QuadraticAlgebra K c b) = star ⟨x 0, x 1⟩ := by
  ext <;> simp [starMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem binF_eq_norm [CharP K 2] (x : Fin 2 → K) :
    binF b c x = (⟨x 0, x 1⟩ : QuadraticAlgebra K c b).norm := by
  rw [binF, QuadraticAlgebra.norm_def]
  linear_combination c * x 1 ^ 2 * CharTwo.two_eq_zero (R := K)

end Mul

section Exists

variable [Finite K] [CharP K 2]

omit [Finite K] in
theorem fact_irred {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Fact (∀ r : K, r ^ 2 ≠ c + b * r) :=
  ⟨fun r hr => hirr r (by linear_combination hr + (c + b * r) * CharTwo.two_eq_zero (R := K))⟩

omit [CharP K 2] in
theorem coprime_two_pow_sub_one {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ n + 1) :
    Nat.Coprime p (2 ^ n - 1) := by
  refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => hp2 ?_
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h2 := Nat.dvd_sub hpn h
  rw [show 2 ^ n + 1 - (2 ^ n - 1) = 2 by omega] at h2
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2

theorem exists_rot {n p : ℕ} (hK : Nat.card K = 2 ^ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ n + 1) :
    ∃ M σ : Matrix.SpecialLinearGroup (Fin 2) K, orderOf M = p ∧ σ * M * σ⁻¹ = M⁻¹ ∧
      (∀ x, binF b c ((M : Matrix (Fin 2) (Fin 2) K) *ᵥ x) = binF b c x) ∧
      (∀ x, binF b c ((σ : Matrix (Fin 2) (Fin 2) K) *ᵥ x) = binF b c x) := by
  have := fact_irred hirr
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (QuadraticAlgebra K c b) :=
    Finite.of_equiv _ (QuadraticAlgebra.equivProd c b).symm
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hdvd : p ∣ Nat.card (QuadraticAlgebra K c b)ˣ := by
    rw [Nat.card_units, Nat.card_congr (QuadraticAlgebra.equivProd c b), Nat.card_prod, hK]
    have h3 : 2 ^ n * 2 ^ n - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
      obtain ⟨k, hk⟩ : ∃ k, 2 ^ n = k + 1 := ⟨2 ^ n - 1, by omega⟩
      rw [hk, Nat.add_sub_cancel]
      ring_nf
      omega
    rw [h3]
    exact Dvd.dvd.mul_right hpn _
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hzp : (z : QuadraticAlgebra K c b) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hz, pow_orderOf_eq_one, Units.val_one]
  have hz1 : (z : QuadraticAlgebra K c b) ≠ 1 := by
    intro h
    have : z = 1 := Units.val_eq_one.mp h
    rw [this, orderOf_one] at hz
    exact hp.one_lt.ne hz
  set ν := (z : QuadraticAlgebra K c b).norm with hν
  have hνp : ν ^ p = 1 := by rw [hν, ← map_pow, hzp, map_one]
  have hν0 : ν ≠ 0 := by
    have : ν * ((z⁻¹ : (QuadraticAlgebra K c b)ˣ) : QuadraticAlgebra K c b).norm = 1 := by
      rw [hν, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
    exact left_ne_zero_of_mul_eq_one this
  have hνq : ν ^ (2 ^ n - 1) = 1 := by
    have := Fintype.ofFinite K
    have := FiniteField.pow_card_sub_one_eq_one ν hν0
    rwa [Fintype.card_eq_nat_card, hK] at this
  have hν1 : ν = 1 := by
    have h := pow_gcd_eq_one.mpr ⟨hνp, hνq⟩
    rwa [(coprime_two_pow_sub_one hp hp2 hpn).gcd_eq_one, pow_one] at h
  let M : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨mulMat (z : QuadraticAlgebra K c b), by rw [det_mulMat, ← hν, hν1]⟩
  let S : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨mulMat (star (z : QuadraticAlgebra K c b)), by
      rw [det_mulMat, QuadraticAlgebra.norm_star, ← hν, hν1]⟩
  let σ : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨starMat b, by rw [starMat, Matrix.det_fin_two_of, mul_zero, sub_zero, mul_neg, mul_one,
      CharTwo.neg_eq]⟩
  have hSM : S * M = 1 := by
    apply Subtype.ext
    change mulMat (star (z : QuadraticAlgebra K c b)) * mulMat (z : QuadraticAlgebra K c b) = 1
    rw [← mulMat_mul, mul_comm, ← QuadraticAlgebra.algebraMap_norm_eq_mul_star, ← hν, hν1,
      map_one, mulMat_one]
  have hMp : M ^ p = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow]
    change (mulMatHom (z : QuadraticAlgebra K c b)) ^ p = 1
    rw [← map_pow, hzp, map_one]
  have hM1 : M ≠ 1 := by
    intro h
    have h0 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) K =>
      (A : Matrix (Fin 2) (Fin 2) K) 0 0) h
    have h10 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) K =>
      (A : Matrix (Fin 2) (Fin 2) K) 1 0) h
    simp only [M, mulMat, Matrix.SpecialLinearGroup.coe_one] at h0 h10
    simp at h0 h10
    exact hz1 (QuadraticAlgebra.ext h0 h10)
  refine ⟨M, σ, orderOf_eq_prime hMp hM1, ?_, fun x => ?_, fun x => ?_⟩
  · have hσ : σ * M = S * σ := Subtype.ext (starMat_mul_mulMat _)
    rw [hσ, mul_inv_cancel_right, eq_inv_of_mul_eq_one_left hSM]
  · rw [binF_eq_norm, binF_eq_norm (c := c)]
    change QuadraticAlgebra.norm ⟨(mulMat (z : QuadraticAlgebra K c b) *ᵥ x) 0,
      (mulMat (z : QuadraticAlgebra K c b) *ᵥ x) 1⟩ = _
    rw [mulMat_mulVec, map_mul, ← hν, hν1, one_mul]
  · rw [binF_eq_norm, binF_eq_norm (c := c)]
    change QuadraticAlgebra.norm ⟨(starMat b *ᵥ x) 0, (starMat b *ᵥ x) 1⟩ = _
    rw [starMat_mulVec (c := c), QuadraticAlgebra.norm_star]

end Exists

end OrthRestTail

end CFSG.StandardType
