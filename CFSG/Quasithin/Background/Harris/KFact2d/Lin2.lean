module

public import Mathlib

public section

open scoped Matrix

namespace CFSG.Quasithin.Background.Harris.KFact2d

variable {F : Type} [Field F]

theorem comm2 {t x : Matrix (Fin 2) (Fin 2) F} (ht : ∀ a : F, t ≠ Matrix.scalar (Fin 2) a)
    (h : x * t = t * x) : ∃ α β : F, x = Matrix.scalar (Fin 2) α + β • t := by
  have hne : t 0 1 ≠ 0 ∨ t 1 0 ≠ 0 ∨ t 0 0 ≠ t 1 1 := by
    by_contra hcon
    simp only [not_or, not_not] at hcon
    obtain ⟨h1, h2, h3⟩ := hcon
    apply ht (t 0 0)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, h1, h2, h3]
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e10 := congrFun (congrFun h 1) 0
  have e11 := congrFun (congrFun h 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  set a := t 0 0
  set b := t 0 1
  set c := t 1 0
  set d := t 1 1
  set p := x 0 0
  set q := x 0 1
  set r := x 1 0
  set s := x 1 1
  have key : ∃ β : F, q = β * b ∧ r = β * c ∧ p - s = β * (a - d) := by
    by_cases hb : b ≠ 0
    · refine ⟨q / b, by field_simp, ?_, ?_⟩
      · field_simp; linear_combination -e00
      · field_simp; linear_combination e01
    · rw [not_not] at hb
      by_cases hc : c ≠ 0
      · refine ⟨r / c, ?_, by field_simp, ?_⟩
        · rw [hb, mul_zero]
          have : q * c = 0 := by rw [hb] at e00; linear_combination e00
          exact (mul_eq_zero.mp this).resolve_right hc
        · field_simp; linear_combination -e10
      · rw [not_not] at hc
        have hd : a ≠ d := by
          rcases hne with h1 | h1 | h1
          · exact absurd hb h1
          · exact absurd hc h1
          · exact h1
        have hda : a - d ≠ 0 := sub_ne_zero.2 hd
        refine ⟨(p - s) / (a - d), ?_, ?_, by field_simp⟩
        · rw [hb, mul_zero]
          rw [hb] at e01
          have : q * (d - a) = 0 := by linear_combination e01
          exact (mul_eq_zero.mp this).resolve_right (fun h0 => hd (by linear_combination -h0))
        · rw [hc, mul_zero]
          rw [hc] at e10
          have : r * (a - d) = 0 := by linear_combination e10
          exact (mul_eq_zero.mp this).resolve_right hda
  obtain ⟨β, hq, hr, hps⟩ := key
  refine ⟨p - β * a, β, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j
  · simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
    show p = (if (0 : Fin 2) = 0 then p - β * a else 0) + β * a
    simp
  · simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
    show q = (if (0 : Fin 2) = 1 then p - β * a else 0) + β * b
    simp [hq]
  · simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
    show r = (if (1 : Fin 2) = 0 then p - β * a else 0) + β * c
    simp [hr]
  · simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
    show s = (if (1 : Fin 2) = 1 then p - β * a else 0) + β * d
    simp
    linear_combination -hps


theorem nonscalar_entries {t : Matrix (Fin 2) (Fin 2) F} (ht : ∀ a : F, t ≠ Matrix.scalar (Fin 2) a) :
    t 0 1 ≠ 0 ∨ t 1 0 ≠ 0 ∨ t 0 0 ≠ t 1 1 := by
  by_contra hcon
  simp only [not_or, not_not] at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  apply ht (t 0 0)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, h1, h2, h3]

theorem sq_comb {t : Matrix (Fin 2) (Fin 2) F} (ht : ∀ a : F, t ≠ Matrix.scalar (Fin 2) a)
    {l : F} (htt : t * t = Matrix.scalar (Fin 2) l) (α β κ : F) (h2 : (2 : F) ≠ 0)
    (h : (Matrix.scalar (Fin 2) α + β • t) * (Matrix.scalar (Fin 2) α + β • t) =
      Matrix.scalar (Fin 2) κ) : α * β = 0 ∧ α ^ 2 + β ^ 2 * l = κ := by
  have hne := nonscalar_entries ht
  have t00 := congrFun (congrFun htt 0) 0
  have t01 := congrFun (congrFun htt 0) 1
  have t10 := congrFun (congrFun htt 1) 0
  have t11 := congrFun (congrFun htt 1) 1
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e10 := congrFun (congrFun h 1) 0
  have e11 := congrFun (congrFun h 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply, Matrix.diagonal_apply] at t00 t01 t10 t11 e00 e01 e10 e11
  have key : 2 * (α * β) = 0 := by
    rcases hne with hb | hc | hd
    · have : 2 * (α * β) * t 0 1 = 0 := by linear_combination e01 - β ^ 2 * t01
      exact (mul_eq_zero.mp this).resolve_right hb
    · have : 2 * (α * β) * t 1 0 = 0 := by linear_combination e10 - β ^ 2 * t10
      exact (mul_eq_zero.mp this).resolve_right hc
    · have : 2 * (α * β) * (t 0 0 - t 1 1) = 0 := by
        linear_combination e00 - e11 - β ^ 2 * t00 + β ^ 2 * t11
      exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.2 hd)
  have hab : α * β = 0 := (mul_eq_zero.mp key).resolve_left h2
  refine ⟨hab, ?_⟩
  linear_combination e00 - β ^ 2 * t00 - 2 * t 0 0 * hab


section GL2

local notation "𝕄" => Matrix (Fin 2) (Fin 2) F

theorem sq_eq_one_iff_of_ne_zero' {β : F} (h : β ^ 2 = 1) : β = 1 ∨ β = -1 := by
  have : (β - 1) * (β + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h1 | h1
  · left; linear_combination h1
  · right; linear_combination h1

theorem scalar_mul_comm (a : F) (M : 𝕄) : Matrix.scalar (Fin 2) a * M = M * Matrix.scalar (Fin 2) a :=
  Matrix.scalar_commute (n := Fin 2) a (fun _ => Commute.all _ _) M

theorem conj_eq_or_neg {A Z : GL (Fin 2) F} (hA : ∀ a : F, (A : 𝕄) ≠ Matrix.scalar (Fin 2) a)
    {l : F} (hAA : (A : 𝕄) * A = Matrix.scalar (Fin 2) l) (hl : l ≠ 0) (h2 : (2 : F) ≠ 0)
    (hcomm : (Z * A * Z⁻¹ : GL (Fin 2) F) * A = A * (Z * A * Z⁻¹)) :
    Z * A * Z⁻¹ = A ∨ Z * A * Z⁻¹ = -A := by
  set B : GL (Fin 2) F := Z * A * Z⁻¹ with hB
  have hBB : (B : 𝕄) * B = Matrix.scalar (Fin 2) l := by
    have hBBg : B * B = Z * (A * A) * Z⁻¹ := by rw [hB]; group
    have h1 : ((B * B : GL (Fin 2) F) : 𝕄) = Matrix.scalar (Fin 2) l := by
      rw [hBBg]
      simp only [Units.val_mul]
      rw [hAA, ← scalar_mul_comm, mul_assoc, Units.mul_inv, mul_one]
    simpa [Units.val_mul] using h1
  have hcomm' : (A : 𝕄) * B = B * A := by
    have := congrArg (fun g : GL (Fin 2) F => (g : 𝕄)) hcomm
    simpa [Units.val_mul] using this.symm
  obtain ⟨α, β, hαβ⟩ := comm2 (t := (A : 𝕄)) (x := (B : 𝕄)) hA hcomm'.symm
  rw [hαβ] at hBB
  obtain ⟨hab, hsq⟩ := sq_comb hA hAA α β l h2 hBB
  rcases mul_eq_zero.mp hab with h0 | h0
  ·
    have hβ : β ^ 2 = 1 := by
      have : β ^ 2 * l = 1 * l := by rw [h0] at hsq; linear_combination hsq
      exact mul_right_cancel₀ hl this
    rcases sq_eq_one_iff_of_ne_zero' hβ with h1 | h1
    · left
      apply Units.ext
      rw [hαβ, h0, h1]; simp
    · right
      apply Units.ext
      rw [hαβ, h0, h1]; simp
  ·
    exfalso
    have hBs : (B : 𝕄) = Matrix.scalar (Fin 2) α := by rw [hαβ, h0]; simp
    apply hA α
    have hAe : (A : 𝕄) = ((Z⁻¹ : GL (Fin 2) F) : 𝕄) * (B : 𝕄) * (Z : 𝕄) := by
      have : A = Z⁻¹ * B * Z := by rw [hB]; group
      conv_lhs => rw [this]
      simp only [Units.val_mul]
    rw [hAe, hBs, ← scalar_mul_comm, mul_assoc, Units.inv_mul, mul_one]


theorem exists_comm_sqm1 {A X Y : GL (Fin 2) F} (G : Subgroup (GL (Fin 2) F)) (hXG : X ∈ G)
    (hYG : Y ∈ G) (hA : ∀ a : F, (A : 𝕄) ≠ Matrix.scalar (Fin 2) a)
    {l : F} (hAA : (A : 𝕄) * A = Matrix.scalar (Fin 2) l) (hl : l ≠ 0) (h2 : (2 : F) ≠ 0)
    (hXX : (X : 𝕄) * X = -1) (hYY : (Y : 𝕄) * Y = -1) (hYX : (Y : 𝕄) * X = -((X : 𝕄) * Y))
    (hX : (X * A * X⁻¹ : GL (Fin 2) F) * A = A * (X * A * X⁻¹))
    (hY : (Y * A * Y⁻¹ : GL (Fin 2) F) * A = A * (Y * A * Y⁻¹)) :
    ∃ x : GL (Fin 2) F, x ∈ G ∧ (x : 𝕄) * x = -1 ∧ x * A = A * x := by
  rcases conj_eq_or_neg hA hAA hl h2 hX with hx | hx
  · exact ⟨X, hXG, hXX, by
      calc X * A = (X * A * X⁻¹) * X := by group
        _ = A * X := by rw [hx]⟩
  rcases conj_eq_or_neg hA hAA hl h2 hY with hy | hy
  · exact ⟨Y, hYG, hYY, by
      calc Y * A = (Y * A * Y⁻¹) * Y := by group
        _ = A * Y := by rw [hy]⟩
  have hXA : X * A = -A * X := by
    calc X * A = (X * A * X⁻¹) * X := by group
      _ = -A * X := by rw [hx]
  have hYA : Y * A = -A * Y := by
    calc Y * A = (Y * A * Y⁻¹) * Y := by group
      _ = -A * Y := by rw [hy]
  refine ⟨X * Y, G.mul_mem hXG hYG, ?_, ?_⟩
  · simp only [Units.val_mul]
    calc (X : 𝕄) * Y * ((X : 𝕄) * Y) = (X : 𝕄) * ((Y : 𝕄) * X) * Y := by noncomm_ring
      _ = -1 := by
        rw [hYX]
        calc (X : 𝕄) * -((X : 𝕄) * Y) * Y = -(((X : 𝕄) * X) * ((Y : 𝕄) * Y)) := by noncomm_ring
          _ = -1 := by rw [hXX, hYY]; simp
  · calc X * Y * A = X * (Y * A) := by group
      _ = X * (-A * Y) := by rw [hYA]
      _ = -(X * A) * Y := by simp [mul_assoc]
      _ = -(-A * X) * Y := by rw [hXA]
      _ = A * (X * Y) := by simp [mul_assoc]

theorem scalar_neg_one : (-1 : 𝕄) = Matrix.scalar (Fin 2) (-1 : F) := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h, Matrix.scalar_apply, Matrix.diagonal_apply]

theorem false_of_sqm1_comm_linear {A x : GL (Fin 2) F}
    (hA : ∀ a : F, (A : 𝕄) ≠ Matrix.scalar (Fin 2) a) {ν : F}
    (hAA : (A : 𝕄) * A = Matrix.scalar (Fin 2) (ν ^ 2)) (h2 : (2 : F) ≠ 0)
    (hns : ∀ y : F, y ^ 2 ≠ -1) (hxx : (x : 𝕄) * x = -1) (hc : x * A = A * x) : False := by
  have hc' : (x : 𝕄) * A = A * x := by
    simpa [Units.val_mul] using congrArg (fun g : GL (Fin 2) F => (g : 𝕄)) hc
  obtain ⟨α, β, hαβ⟩ := comm2 (t := (A : 𝕄)) (x := (x : 𝕄)) hA hc'
  rw [hαβ, scalar_neg_one] at hxx
  obtain ⟨hab, hsq⟩ := sq_comb hA hAA α β (-1) h2 hxx
  rcases mul_eq_zero.mp hab with h0 | h0
  · rw [h0] at hsq
    exact hns (β * ν) (by linear_combination hsq)
  · rw [h0] at hsq
    exact hns α (by linear_combination hsq)


theorem false_of_sqm1_comm_unitary {p : ℕ} [Fact p.Prime] {A x : GL (Fin 2) F}
    (hA : ∀ a : F, (A : 𝕄) ≠ Matrix.scalar (Fin 2) a) {l : F}
    (hAA : (A : 𝕄) * A = Matrix.scalar (Fin 2) l) (hl3 : l ^ 3 = 1) (h2 : (2 : F) ≠ 0)
    {m : ℕ} (hm : p + 1 = 2 * m) (hmo : Odd m)
    (hAu : (((A : 𝕄).map (· ^ p))ᵀ * (A : 𝕄) = 1))
    (hxu : (((x : 𝕄).map (· ^ p))ᵀ * (x : 𝕄) = 1))
    (hxx : (x : 𝕄) * x = -1) (hc : x * A = A * x) : False := by
  have hc' : (x : 𝕄) * A = A * x := by
    simpa [Units.val_mul] using congrArg (fun g : GL (Fin 2) F => (g : 𝕄)) hc
  obtain ⟨α, β, hαβ⟩ := comm2 (t := (A : 𝕄)) (x := (x : 𝕄)) hA hc'
  rw [hαβ, scalar_neg_one] at hxx
  obtain ⟨hab, hsq⟩ := sq_comb hA hAA α β (-1) h2 hxx
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hneg : (-1 : F) ^ m = -1 := hmo.neg_one_pow
  have h2' : (2 : F) = 0 → False := h2
  rcases mul_eq_zero.mp hab with h0 | h0
  ·
    rw [h0] at hsq
    rw [hαβ, h0] at hxu
    have e := congrFun (congrFun hxu 0) 0
    have eA := congrFun (congrFun hAu 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two, mul_pow] at e eA
    have hβ : β ^ (p + 1) = 1 := by
      have : β ^ (p + 1) * ((A : 𝕄) 0 0 ^ p * (A : 𝕄) 0 0 + (A : 𝕄) 1 0 ^ p * (A : 𝕄) 1 0) = 1 := by
        rw [pow_succ]; linear_combination e
      rw [eA, mul_one] at this
      exact this
    have hlm : l ^ m = -1 := by
      have h1 : (β ^ 2 * l) ^ m = -1 := by
        have : β ^ 2 * l = -1 := by linear_combination hsq
        rw [this, hneg]
      rw [mul_pow, ← pow_mul, ← hm, hβ, one_mul] at h1
      exact h1
    have h3 : (l ^ m) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hl3, one_pow]
    rw [hlm] at h3
    exact h2' (by linear_combination -h3)
  ·
    rw [h0] at hsq
    rw [hαβ, h0] at hxu
    have e := congrFun (congrFun hxu 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply, Matrix.diagonal_apply,
      zero_pow hp0] at e
    have hα : α ^ (p + 1) = 1 := by rw [pow_succ]; exact e
    have hα2 : α ^ (p + 1) = -1 := by
      rw [hm, pow_mul]
      have : α ^ 2 = -1 := by linear_combination hsq
      rw [this, hneg]
    exact h2' (by linear_combination hα2 - hα)

end GL2



end CFSG.Quasithin.Background.Harris.KFact2d
