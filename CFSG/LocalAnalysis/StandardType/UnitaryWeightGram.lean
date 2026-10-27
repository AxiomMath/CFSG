module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Diagonal
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.StandardType

namespace UnitaryWeight

open Matrix

section Gram

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : Type*} [Field Ω]

theorem isUnit_gram_weight (σ : Ω ≃+* Ω) {P G : Matrix ι ι Ω} (hP : IsUnit P) (hG : IsUnit G) :
    IsUnit (Pᵀ * G * P.map σ) := by
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hGd : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hG
  have hPσd : IsUnit (P.map σ).det := by
    rw [← RingEquiv.coe_toRingHom σ]
    rw [← RingHom.mapMatrix_apply (σ : Ω →+* Ω) P]
    rw [← RingHom.map_det (σ : Ω →+* Ω) P]
    exact IsUnit.map (σ : Ω →+* Ω) hPd
  rw [Matrix.isUnit_iff_isUnit_det]
  simp only [Matrix.det_mul, Matrix.det_transpose]
  exact (hPd.mul hGd).mul hPσd

theorem gram_weight_entry (σ : Ω ≃+* Ω) {P X G : Matrix ι ι Ω} {w : ι → Ω} {s : Ω}
    (hX : Xᵀ * G * X.map σ = s • G) (hP : X * P = P * diagonal w) {α β : ι}
    (h : (Pᵀ * G * P.map σ) α β ≠ 0) : w α * σ (w β) = s := by
  set H : Matrix ι ι Ω := Pᵀ * G * P.map σ with hH
  have hPt : Pᵀ * Xᵀ = diagonal w * Pᵀ := by
    have h' := congrArg Matrix.transpose hP
    rwa [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.diagonal_transpose] at h'
  have hPσ : X.map σ * P.map σ = P.map σ * diagonal (fun i => σ (w i)) := by
    have h' := congrArg (fun M : Matrix ι ι Ω => M.map σ) hP
    rwa [Matrix.map_mul, Matrix.map_mul, Matrix.diagonal_map (σ.map_zero)] at h'
  have hkey : s • H = diagonal w * H * diagonal (fun i => σ (w i)) := by
    rw [hH]
    calc s • (Pᵀ * G * P.map σ)
        = Pᵀ * (s • G) * P.map σ := by
            simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = Pᵀ * (Xᵀ * G * X.map σ) * P.map σ := by rw [← hX]
      _ = diagonal w * (Pᵀ * G * P.map σ) * diagonal (fun i => σ (w i)) := by
            calc Pᵀ * (Xᵀ * G * X.map σ) * P.map σ
                = (Pᵀ * Xᵀ) * G * X.map σ * P.map σ := by noncomm_ring
              _ = (diagonal w * Pᵀ) * G * X.map σ * P.map σ := by rw [hPt]
              _ = diagonal w * Pᵀ * G * (X.map σ * P.map σ) := by noncomm_ring
              _ = diagonal w * Pᵀ * G * (P.map σ * diagonal (fun i => σ (w i))) := by
                    rw [hPσ]
              _ = diagonal w * (Pᵀ * G * P.map σ) * diagonal (fun i => σ (w i)) := by
                    noncomm_ring
  have he := congrArg (fun M : Matrix ι ι Ω => M α β) hkey
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_mul, Matrix.mul_diagonal] at he
  have hcancel : H α β * s = H α β * (w α * σ (w β)) := by
    rw [mul_comm (H α β) s, he]
    ring
  exact (mul_left_cancel₀ h hcancel).symm

theorem transport_form (σ : Ω ≃+* Ω) {P Q R G : Matrix ι ι Ω} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hR : Rᵀ * G * R.map σ = G) :
    (Q * R * P)ᵀ * (Pᵀ * G * P.map σ) * (Q * R * P).map σ = Pᵀ * G * P.map σ := by
  have hQPt : Qᵀ * Pᵀ = 1 := by
    rw [← Matrix.transpose_mul, hPQ]
    simp
  have hPσQσ : P.map σ * Q.map σ = 1 := by
    rw [← Matrix.map_mul, hPQ]
    simp
  calc (Q * R * P)ᵀ * (Pᵀ * G * P.map σ) * (Q * R * P).map σ
      = Pᵀ * Rᵀ * Qᵀ * (Pᵀ * G * P.map σ) * (Q.map σ * R.map σ * P.map σ) := by
          rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.map_mul, Matrix.map_mul]
          noncomm_ring
    _ = Pᵀ * Rᵀ * (Qᵀ * Pᵀ) * G * (P.map σ * Q.map σ) * R.map σ * P.map σ := by
          noncomm_ring
    _ = Pᵀ * Rᵀ * G * R.map σ * P.map σ := by rw [hQPt, hPσQσ]; noncomm_ring
    _ = Pᵀ * (Rᵀ * G * R.map σ) * P.map σ := by noncomm_ring
    _ = Pᵀ * G * P.map σ := by rw [hR]

theorem commute_diagonal_conj {P Q X R : Matrix ι ι Ω} {w : ι → Ω} (hPQ : P * Q = 1)
    (hQP : Q * P = 1) (hP : X * P = P * diagonal w) (hc : R * X = X * R) :
    (Q * R * P) * diagonal w = diagonal w * (Q * R * P) := by
  have hQXP : Q * X * P = diagonal w := by
    calc Q * X * P = Q * (X * P) := by noncomm_ring
      _ = Q * (P * diagonal w) := by rw [hP]
      _ = (Q * P) * diagonal w := by noncomm_ring
      _ = diagonal w := by rw [hQP, Matrix.one_mul]
  calc (Q * R * P) * diagonal w
      = Q * R * (P * diagonal w) := by noncomm_ring
    _ = Q * R * (X * P) := by rw [hP]
    _ = Q * (R * X) * P := by noncomm_ring
    _ = Q * (X * R) * P := by rw [hc]
    _ = Q * X * (P * Q) * R * P := by rw [hPQ]; noncomm_ring
    _ = (Q * X * P) * (Q * R * P) := by noncomm_ring
    _ = diagonal w * (Q * R * P) := by rw [hQXP]

end Gram

section Frobenius

variable {Ω : Type*} [Field Ω] [CharP Ω 2]

theorem ringEquiv_apply_eq_two_pow_of_pow_seven (σ : Ω ≃+* Ω) {η : Ω} (hη : η ^ 7 = 1) :
    ∃ k : ℕ, σ η = η ^ 2 ^ k := by
  set e₁ : Ω := η + η ^ 2 + η ^ 4 with he₁
  set e₂ : Ω := η ^ 3 + η ^ 5 + η ^ 6 with he₂
  have hη8 : η ^ 8 = η := by
    rw [show (8 : ℕ) = 1 + 7 by norm_num, pow_add, hη, mul_one, pow_one]
  have hη10 : η ^ 10 = η ^ 3 := by
    rw [show (10 : ℕ) = 3 + 7 by norm_num, pow_add, hη, mul_one]
  have hη12 : η ^ 12 = η ^ 5 := by
    rw [show (12 : ℕ) = 5 + 7 by norm_num, pow_add, hη, mul_one]
  have he₁_sq : e₁ ^ 2 = e₁ := by
    rw [he₁]
    have hexp : (η + η ^ 2 + η ^ 4) ^ 2
        = η ^ 2 + η ^ 4 + η ^ 8 + 2 * (η * η ^ 2 + η * η ^ 4 + η ^ 2 * η ^ 4) := by ring
    rw [hexp, hη8]
    rw [show (2 : Ω) = 0 from CharP.cast_eq_zero Ω 2]
    ring
  have he₂_sq : e₂ ^ 2 = e₂ := by
    rw [he₂]
    have hexp : (η ^ 3 + η ^ 5 + η ^ 6) ^ 2
        = η ^ 6 + η ^ 10 + η ^ 12
          + 2 * (η ^ 3 * η ^ 5 + η ^ 3 * η ^ 6 + η ^ 5 * η ^ 6) := by ring
    rw [hexp, hη10, hη12]
    rw [show (2 : Ω) = 0 from CharP.cast_eq_zero Ω 2]
    ring
  have he₁_cases : e₁ = 0 ∨ e₁ = 1 := by
    have h : e₁ * (e₁ - 1) = 0 := by rw [mul_sub, mul_one, ← pow_two, he₁_sq, sub_self]
    rcases mul_eq_zero.mp h with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1)
  have he₂_cases : e₂ = 0 ∨ e₂ = 1 := by
    have h : e₂ * (e₂ - 1) = 0 := by rw [mul_sub, mul_one, ← pow_two, he₂_sq, sub_self]
    rcases mul_eq_zero.mp h with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1)
  have hσe₁ : σ e₁ = e₁ := by
    rcases he₁_cases with h | h <;> rw [h] <;> simp
  have hσe₂ : σ e₂ = e₂ := by
    rcases he₂_cases with h | h <;> rw [h] <;> simp
  have hpoly : ∀ T : Ω, (T - η) * (T - η ^ 2) * (T - η ^ 4)
      = T ^ 3 - e₁ * T ^ 2 + e₂ * T - η ^ 7 := by
    intro T
    rw [he₁, he₂]
    ring
  have hroot : η ^ 3 - e₁ * η ^ 2 + e₂ * η - 1 = 0 := by
    have h := hpoly η
    simp only [sub_self, zero_mul, hη] at h
    exact h.symm
  have hrootσ : (σ η) ^ 3 - e₁ * (σ η) ^ 2 + e₂ * (σ η) - 1 = 0 := by
    have h := congrArg σ hroot
    simpa only [map_sub, map_add, map_mul, map_pow, map_one, map_zero, hσe₁, hσe₂] using h
  have hprod : (σ η - η) * (σ η - η ^ 2) * (σ η - η ^ 4) = 0 := by
    have h := hpoly (σ η)
    rw [hη] at h
    rw [hrootσ] at h
    exact h
  rcases mul_eq_zero.mp hprod with h | h4
  · rcases mul_eq_zero.mp h with h1 | h2
    · refine ⟨0, ?_⟩
      rw [show (2 : ℕ) ^ 0 = 1 by norm_num, pow_one]
      exact sub_eq_zero.mp h1
    · refine ⟨1, ?_⟩
      rw [show (2 : ℕ) ^ 1 = 2 by norm_num]
      exact sub_eq_zero.mp h2
  · refine ⟨2, ?_⟩
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num]
    exact sub_eq_zero.mp h4

end Frobenius

end UnitaryWeight

end CFSG.StandardType
