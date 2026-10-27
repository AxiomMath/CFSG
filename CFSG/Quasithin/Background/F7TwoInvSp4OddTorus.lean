module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpOuter

public section

namespace CFSG.Quasithin.F7Two

open Matrix CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

variable {K : Type} [Field K]

@[expose] def torMat (t₁ t₂ : Kˣ) : Matrix (Fin 4) (Fin 4) K :=
  Matrix.diagonal ![(t₁ : K), (t₂ : K), ((t₂⁻¹ : Kˣ) : K), ((t₁⁻¹ : Kˣ) : K)]

theorem torMat_mul (t₁ t₂ s₁ s₂ : Kˣ) :
    torMat t₁ t₂ * torMat s₁ s₂ = (torMat (t₁ * s₁) (t₂ * s₂) : Matrix (Fin 4) (Fin 4) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [torMat, Matrix.diagonal_apply, Matrix.mul_apply, mul_comm]

theorem torMat_one : torMat (1 : Kˣ) (1 : Kˣ) = (1 : Matrix (Fin 4) (Fin 4) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [torMat]

theorem torMat_mem [CharP K 2] (t₁ t₂ : Kˣ) :
    (torMat t₁ t₂ : Matrix (Fin 4) (Fin 4) K)ᵀ * minorJ K * torMat t₁ t₂ = minorJ K := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [torMat, Matrix.diagonal_apply, Matrix.mul_apply,
    Fin.sum_univ_four, minorJ_apply]

@[expose] def torElt [CharP K 2] (t₁ t₂ : Kˣ) : antiSp K :=
  ⟨⟨torMat t₁ t₂, torMat t₁⁻¹ t₂⁻¹, by
      rw [torMat_mul, mul_inv_cancel, mul_inv_cancel, torMat_one],
    by rw [torMat_mul, inv_mul_cancel, inv_mul_cancel, torMat_one]⟩, torMat_mem t₁ t₂⟩

theorem torElt_inv [CharP K 2] (t₁ t₂ : Kˣ) :
    (torElt t₁ t₂ : antiSp K)⁻¹ = torElt t₁⁻¹ t₂⁻¹ :=
  antiSp_ext rfl

theorem torElt_mul [CharP K 2] (t₁ t₂ s₁ s₂ : Kˣ) :
    (torElt t₁ t₂ : antiSp K) * torElt s₁ s₂ = torElt (t₁ * s₁) (t₂ * s₂) :=
  antiSp_ext (torMat_mul t₁ t₂ s₁ s₂)

theorem torElt_one [CharP K 2] : (torElt 1 1 : antiSp K) = 1 :=
  antiSp_ext torMat_one

variable (K) in
@[expose] def torHom [CharP K 2] : Kˣ × Kˣ →* antiSp K where
  toFun t := torElt t.1 t.2
  map_one' := torElt_one
  map_mul' s t := (torElt_mul s.1 s.2 t.1 t.2).symm

variable (K) in
@[expose] def antiTorus [CharP K 2] : Subgroup (antiSp K) := (torHom K).range

theorem torElt_mem_antiTorus [CharP K 2] (t₁ t₂ : Kˣ) : (torElt t₁ t₂ : antiSp K) ∈ antiTorus K :=
  ⟨(t₁, t₂), rfl⟩

theorem odd_natCard_antiTorus [CharP K 2] [Finite K] {q : ℕ} (hK : Nat.card K = q) (hq : Even q)
    (hq1 : 1 ≤ q) : Odd (Nat.card (antiTorus K)) := by
  have hdvd : Nat.card (antiTorus K) ∣ Nat.card (Kˣ × Kˣ) :=
    Subgroup.card_dvd_of_surjective (MonoidHom.rangeRestrict_surjective (torHom K))
  have hodd : Odd (Nat.card (Kˣ × Kˣ)) := by
    rw [Nat.card_prod, Nat.card_units, hK]
    exact (Nat.Even.sub_odd hq1 hq odd_one).mul (Nat.Even.sub_odd hq1 hq odd_one)
  exact hodd.of_dvd_nat hdvd

theorem torElt_mul_uElt_mul_inv [CharP K 2] (t₁ t₂ : Kˣ) (b c : K) :
    (torElt t₁ t₂ : antiSp K) * uElt 0 b c 0 * (torElt t₁ t₂)⁻¹ =
      uElt 0 (t₁ * t₂ * b) (t₁ ^ 2 * c) 0 := by
  rw [torElt_inv]
  refine antiSp_ext ?_
  change torMat t₁ t₂ * uMat 0 b c 0 * torMat t₁⁻¹ t₂⁻¹ = uMat 0 (t₁ * t₂ * b) (t₁ ^ 2 * c) 0
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [torMat, uMat, Matrix.mul_apply, Matrix.diagonal_apply] <;>
    field_simp

theorem minorMap_diagonal (d : Fin 4 → K) :
    minorMap (Matrix.diagonal d) =
      Matrix.diagonal ![d 0 * d 1, d 0 * d 2, d 1 * d 3, d 2 * d 3] := by
  ext A B
  fin_cases A <;> fin_cases B <;> simp [minorMap_apply, minorIdx_zero, minorIdx_one, minorIdx_two,
    minorIdx_three]

theorem eta_torElt [CharP K 2] [Finite K] (m : ℕ) (t₁ t₂ : Kˣ) :
    (minorAut K ^ (2 * m + 1)) (torElt t₁ t₂) =
      torElt (t₁ ^ 2 ^ m * t₂ ^ 2 ^ m) (t₁ ^ 2 ^ m * (t₂ ^ 2 ^ m)⁻¹) := by
  refine antiSp_ext ?_
  rw [glMat_eta]
  change minorMap ((torMat t₁ t₂).map (· ^ 2 ^ m)) =
    torMat (t₁ ^ 2 ^ m * t₂ ^ 2 ^ m) (t₁ ^ 2 ^ m * (t₂ ^ 2 ^ m)⁻¹)
  have h1 : (torMat t₁ t₂).map (· ^ 2 ^ m) = Matrix.diagonal
      ![(t₁ : K) ^ 2 ^ m, (t₂ : K) ^ 2 ^ m, ((t₂⁻¹ : Kˣ) : K) ^ 2 ^ m,
        ((t₁⁻¹ : Kˣ) : K) ^ 2 ^ m] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [torMat]
  rw [h1, minorMap_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [torMat]

@[expose] def jElt : antiSp K :=
  ⟨⟨minorJ K, minorJ K, minorJ_mul_self, minorJ_mul_self⟩, by
    change (minorJ K)ᵀ * minorJ K * minorJ K = minorJ K
    rw [minorJ_transpose, minorJ_mul_self, Matrix.one_mul]⟩

theorem glMat_jElt : glMat (jElt : antiSp K).1 = minorJ K :=
  rfl

theorem jElt_inv : (jElt : antiSp K)⁻¹ = jElt :=
  antiSp_ext rfl

theorem jElt_mul_self : (jElt : antiSp K) * jElt = 1 :=
  antiSp_ext minorJ_mul_self

theorem minorMap_minorJ [CharP K 2] : minorMap (minorJ K) = minorJ K := by
  have h1 : (-1 : K) = 1 := CharTwo.neg_eq 1
  ext A B
  fin_cases A <;> fin_cases B <;> simp [minorMap_apply, minorIdx_zero, minorIdx_one, minorIdx_two,
    minorIdx_three, minorJ_apply, h1]

theorem eta_jElt [CharP K 2] [Finite K] (m : ℕ) :
    (minorAut K ^ (2 * m + 1)) jElt = jElt := by
  refine antiSp_ext ?_
  rw [glMat_eta]
  have h1 : (glMat (jElt : antiSp K).1).map (· ^ 2 ^ m) = minorJ K := by
    ext i j
    simp only [Matrix.map_apply, glMat_jElt, minorJ_apply]
    split_ifs
    · exact one_pow _
    · exact zero_pow (pow_ne_zero _ two_ne_zero)
  rw [h1, minorMap_minorJ]
  rfl

@[expose] def zElt [CharP K 2] (m : ℕ) (c : K) : antiSp K := uElt 0 (c ^ 2 ^ m) c 0

theorem eta_zElt [CharP K 2] [Finite K] (m : ℕ) (hK : Nat.card K = 2 ^ (2 * m + 1)) (c : K) :
    (minorAut K ^ (2 * m + 1)) (zElt m c) = zElt m c := by
  have : Fintype K := Fintype.ofFinite K
  have h0e : (0 : K) ^ 2 ^ m = 0 := zero_pow (pow_ne_zero _ two_ne_zero)
  have hc : ((c ^ 2 ^ m) ^ 2 ^ m) ^ 2 = c := by
    rw [← pow_mul, ← pow_mul, show 2 ^ m * (2 ^ m * 2) = 2 ^ (2 * m + 1) by
      rw [pow_succ, pow_mul']; ring, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  refine antiSp_ext ?_
  rw [zElt, glMat_eta_uElt, h0e, glMat_uElt, hc]
  congr 1 <;> ring

end CFSG.Quasithin.F7Two
