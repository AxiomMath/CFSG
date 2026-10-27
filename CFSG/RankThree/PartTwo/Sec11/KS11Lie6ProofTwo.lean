module

public import Mathlib.LinearAlgebra.Matrix.CharP
public import CFSG.LieType.Chevalley.RankOneGaussian

public section

namespace CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof

open Matrix
open CFSG.LieType.Chevalley
open scoped MatrixGroups

variable {L : Type} [Field L]

theorem not_scalar_of_pow_three {Z : SL2 L} (hZ3 : Z ^ 3 = 1) (hZ1 : Z ≠ 1) :
    ¬ ((Z : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 ∧ (Z : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
      (Z : Matrix (Fin 2) (Fin 2) L) 0 0 = (Z : Matrix (Fin 2) (Fin 2) L) 1 1) := by
  rintro ⟨h01, h10, h00⟩
  set c := (Z : Matrix (Fin 2) (Fin 2) L) 0 0 with hc
  have hZc : (Z : Matrix (Fin 2) (Fin 2) L) = c • 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h10, ← h00, hc]
  have hdet : c ^ 2 = 1 := by
    have h := Z.2
    rw [hZc, Matrix.det_smul, Matrix.det_one, mul_one] at h
    simpa using h
  have hcube : c ^ 3 = 1 := by
    have h := congrArg (fun X : SL2 L => (X : Matrix (Fin 2) (Fin 2) L) 0 0) hZ3
    simp only [Matrix.SpecialLinearGroup.coe_pow, hZc, smul_pow, one_pow,
      Matrix.SpecialLinearGroup.coe_one] at h
    simpa using h
  have hc1 : c = 1 := by
    calc c = c * c ^ 2 := by rw [hdet, mul_one]
      _ = c ^ 3 := by ring
      _ = 1 := hcube
  apply hZ1
  exact Subtype.ext (by rw [hZc, hc1, one_smul, Matrix.SpecialLinearGroup.coe_one])

theorem exists_smul_add_of_commute {Y Z : Matrix (Fin 2) (Fin 2) L} (hYZ : Y * Z = Z * Y)
    (hZ : ¬ (Z 0 1 = 0 ∧ Z 1 0 = 0 ∧ Z 0 0 = Z 1 1)) : ∃ α β : L, Y = α • 1 + β • Z := by
  have e : ∀ i j, (Y * Z) i j = (Z * Y) i j := fun i j => by rw [hYZ]
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10
  by_cases h01 : Z 0 1 = 0
  · by_cases h10 : Z 1 0 = 0
    · have hd : Z 0 0 - Z 1 1 ≠ 0 := fun h => hZ ⟨h01, h10, sub_eq_zero.1 h⟩
      have y01 : Y 0 1 = 0 := by
        have : Y 0 1 * (Z 0 0 - Z 1 1) = 0 := by rw [h01] at e01; linear_combination -e01
        exact (mul_eq_zero.1 this).resolve_right hd
      have y10 : Y 1 0 = 0 := by
        have : Y 1 0 * (Z 0 0 - Z 1 1) = 0 := by rw [h10] at e10; linear_combination e10
        exact (mul_eq_zero.1 this).resolve_right hd
      have key : (Y 0 0 - Y 1 1) / (Z 0 0 - Z 1 1) * (Z 0 0 - Z 1 1) = Y 0 0 - Y 1 1 :=
        div_mul_cancel₀ _ hd
      refine ⟨Y 0 0 - (Y 0 0 - Y 1 1) / (Z 0 0 - Z 1 1) * Z 0 0,
        (Y 0 0 - Y 1 1) / (Z 0 0 - Z 1 1), ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h01, h10, y01, y10]
      linear_combination key
    · have key : Y 1 0 / Z 1 0 * Z 1 0 = Y 1 0 := div_mul_cancel₀ _ h10
      have y01 : Y 0 1 = 0 := by
        have : Y 0 1 * Z 1 0 = 0 := by rw [h01] at e00; linear_combination e00
        exact (mul_eq_zero.1 this).resolve_right h10
      have key2 : Y 1 0 / Z 1 0 * (Z 0 0 - Z 1 1) = Y 0 0 - Y 1 1 := by
        rw [div_mul_eq_mul_div, div_eq_iff h10]
        linear_combination e10
      refine ⟨Y 0 0 - Y 1 0 / Z 1 0 * Z 0 0, Y 1 0 / Z 1 0, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h01, y01]
      · linear_combination -key
      · linear_combination key2
  · have key : Y 0 1 / Z 0 1 * Z 0 1 = Y 0 1 := div_mul_cancel₀ _ h01
    have key1 : Y 0 1 / Z 0 1 * Z 1 0 = Y 1 0 := by
      rw [div_mul_eq_mul_div, div_eq_iff h01]
      linear_combination e00
    have key2 : Y 0 1 / Z 0 1 * (Z 0 0 - Z 1 1) = Y 0 0 - Y 1 1 := by
      rw [div_mul_eq_mul_div, div_eq_iff h01]
      linear_combination -e01
    refine ⟨Y 0 0 - Y 0 1 / Z 0 1 * Z 0 0, Y 0 1 / Z 0 1, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    · linear_combination -key
    · linear_combination -key1
    · linear_combination key2

theorem frob_fixed_of_smul_add (Fr : L →+* L) {Z : Matrix (Fin 2) (Fin 2) L}
    (hZ : ¬ (Z 0 1 = 0 ∧ Z 1 0 = 0 ∧ Z 0 0 = Z 1 1)) (hFZ : ∀ i j, Fr (Z i j) = Z i j)
    {α β : L} (hFY : ∀ i j, Fr ((α • 1 + β • Z) i j) = (α • 1 + β • Z) i j) :
    Fr α = α ∧ Fr β = β := by
  have y00 := hFY 0 0
  have y01 := hFY 0 1
  have y10 := hFY 1 0
  have y11 := hFY 1 1
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, Matrix.one_apply_ne,
    ne_eq, Fin.isValue, zero_ne_one, not_false_eq_true, one_ne_zero, smul_eq_mul,
    mul_one, mul_zero, zero_add, map_add, map_mul, hFZ] at y00 y01 y10 y11
  have hβ : Fr β = β := by
    by_cases h01 : Z 0 1 = 0
    · by_cases h10 : Z 1 0 = 0
      · have hd : Z 0 0 - Z 1 1 ≠ 0 := fun h => hZ ⟨h01, h10, sub_eq_zero.1 h⟩
        have : (Fr β - β) * (Z 0 0 - Z 1 1) = 0 := by linear_combination y00 - y11
        exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hd)
      · have : (Fr β - β) * Z 1 0 = 0 := by linear_combination y10
        exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right h10)
    · have : (Fr β - β) * Z 0 1 = 0 := by linear_combination y01
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right h01)
  refine ⟨?_, hβ⟩
  rw [hβ] at y00
  linear_combination y00

variable {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

theorem pow_sq_sub_one_eq_one (hℓ3 : ℓ ≠ 3) {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    {Y Z : SL2 L} (hZ3 : Z ^ 3 = 1) (hZ1 : Z ≠ 1)
    (hFZ : Matrix.SpecialLinearGroup.map Fr Z = Z) (hFY : Matrix.SpecialLinearGroup.map Fr Y = Y)
    (hYZ : Y * Z = Z * Y) : Y ^ ((ℓ ^ f) ^ 2 - 1) = 1 := by
  have hℓ : ℓ.Prime := Fact.out
  have hZ := not_scalar_of_pow_three hZ3 hZ1
  have hent : ∀ (X : SL2 L), Matrix.SpecialLinearGroup.map Fr X = X →
      ∀ i j, Fr ((X : Matrix (Fin 2) (Fin 2) L) i j) = (X : Matrix (Fin 2) (Fin 2) L) i j := by
    intro X hX i j
    have := congrArg (fun W : SL2 L => (W : Matrix (Fin 2) (Fin 2) L) i j) hX
    simpa only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply] using this
  obtain ⟨α, β, hαβ⟩ := exists_smul_add_of_commute
    (congrArg (fun W : SL2 L => (W : Matrix (Fin 2) (Fin 2) L)) hYZ) hZ
  obtain ⟨hα, hβ⟩ := frob_fixed_of_smul_add Fr hZ (hent Z hFZ) (α := α) (β := β)
    (fun i j => by rw [← hαβ]; exact hent Y hFY i j)
  have hq3 : ¬ 3 ∣ ℓ ^ f := fun h => hℓ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1
    (Nat.prime_three.dvd_of_dvd_pow h)).symm
  have hsq : (ℓ ^ f) ^ 2 % 3 = 1 := by
    have : ℓ ^ f % 3 = 1 ∨ ℓ ^ f % 3 = 2 := by omega
    rw [Nat.pow_mod]
    rcases this with h | h <;> rw [h]
  have hfix2 : ∀ c : L, Fr c = c → c ^ (ℓ ^ (2 * f)) = c := by
    intro c hc
    have h1 : c ^ ℓ ^ f = c := by rw [← hFr]; exact hc
    have e : ℓ ^ (2 * f) = ℓ ^ f * ℓ ^ f := by rw [two_mul, pow_add]
    rw [e, pow_mul, h1, h1]
  have hZq : (Z : Matrix (Fin 2) (Fin 2) L) ^ (ℓ ^ (2 * f)) = Z := by
    have e : ℓ ^ (2 * f) = 3 * ((ℓ ^ (2 * f)) / 3) + 1 := by
      have : ℓ ^ (2 * f) = (ℓ ^ f) ^ 2 := by rw [← pow_mul, mul_comm]
      omega
    rw [← Matrix.SpecialLinearGroup.coe_pow, e, pow_succ, pow_mul, hZ3, one_pow, one_mul]
  have hYq : (Y : Matrix (Fin 2) (Fin 2) L) ^ (ℓ ^ (2 * f)) = Y := by
    have hc : Commute (α • (1 : Matrix (Fin 2) (Fin 2) L)) (β • (Z : Matrix (Fin 2) (Fin 2) L)) :=
      ((Commute.one_left _).smul_left α).smul_right β
    rw [hαβ, add_pow_char_pow_of_commute ℓ (2 * f) hc, smul_pow, smul_pow, one_pow, hZq,
      hfix2 α hα, hfix2 β hβ]
  have hYq' : Y ^ (ℓ ^ (2 * f)) = Y := Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_pow, hYq])
  have hpos : 1 ≤ (ℓ ^ f) ^ 2 := Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have e2 : ℓ ^ (2 * f) = (ℓ ^ f) ^ 2 - 1 + 1 := by
    rw [Nat.sub_add_cancel hpos, ← pow_mul, mul_comm]
  rw [e2, pow_succ] at hYq'
  exact mul_eq_right.1 hYq'

end CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof
