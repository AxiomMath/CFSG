module

public import CFSG.Walter.ReeOrder.Ward.ArithEight

public section

namespace CFSG.Walter.WardLocal

open CFSG.Walter.Ward

theorem block_arith {p mm : ℕ} (hp : p.Prime) {q a d₂ d₃ d₄ δ₂ δ₃ δ₄ e₂ e₃ e₄ D R : ℤ}
    (hqpm : q = (p : ℤ) ^ mm) (hq : 27 ≤ q) (hq8 : q % 8 = 4 + -1) (ha : 0 < a)
    (h₂ : IsSign δ₂) (h₃ : IsSign δ₃) (h₄ : IsSign δ₄)
    (pd₂ : 0 < d₂) (pd₃ : 0 < d₃) (pd₄ : 0 < d₄) (hD : D ≠ 0)
    (h6 : ((q ^ 3 * (q ^ 2 - 1) * a : ℤ) : ℚ) *
      (1 + δ₂ / d₂ + δ₃ * q ^ 2 / d₃ + δ₄ * q ^ 2 / d₄) = q ^ 2 * (q ^ 2 - 1) ^ 2 * (q + -1))
    (h8 : ((q : ℚ) + -1) * (q * (q ^ 2 - 1)) ^ 2 = ((q ^ 3 * (q ^ 2 - 1) * a : ℤ) : ℚ) *
      (2 * (q - -1) ^ 2 * (-1) / D + 1 + e₂ / d₂ + e₃ * q ^ 2 / d₃ + e₄ * q ^ 2 / d₄))
    (R1 : 1 + δ₂ * e₂ + δ₃ * e₃ + δ₄ * e₄ = 0)
    (R2 : 2 * (-1) * D + 1 + e₂ * d₂ + e₃ * d₃ + e₄ * d₄ = 0)
    (R3 : 1 + δ₂ * d₂ + δ₃ * d₃ + δ₄ * d₄ = 0)
    (O2 : δ₃ * e₃ + δ₄ * e₄ = 0) (FS : 1 + δ₂ + δ₃ + δ₄ = 0)
    (hR : 2 * R = q + -1) (hRo : R ∣ d₂ - e₂) (hpar : ∃ k, d₂ = δ₂ + 2 * k)
    (hsyl : (8 : ℤ) ∣ d₂ + 7 * δ₂) (hint₃ : d₃ ∣ q ^ 2 * a * (-(-1) * q * δ₃))
    (hσ : δ₃ = e₃) :
    δ₂ = -1 ∧ δ₃ = 1 ∧ δ₄ = -1 ∧ e₂ = 1 ∧ e₃ = 1 ∧ e₄ = 1 ∧ d₂ = q ^ 2 - q + 1 ∧
      d₃ = q ^ 3 ∧ d₄ = q * (q ^ 2 - q + 1) ∧ D = q ^ 3 + 1 ∧ a = q ^ 2 - q + 1 := by
  have he : IsSign (-1 : ℤ) := Or.inr rfl
  have hg : q ^ 3 * (q ^ 2 - 1) * a ≠ 0 := by
    have : 0 < q ^ 2 - 1 := by nlinarith
    positivity
  obtain ⟨he₂, he₄, hδ₃, hδ₄, hd₄, hd₃⟩ := eight_signs hq he h₂ h₃ h₄ pd₂ pd₃ pd₄ hD hg h6 h8 R1
    R2 R3 O2 hσ
  have hδ₂ : δ₂ = -1 := by
    rw [hδ₃, hδ₄] at FS
    linarith
  rw [hδ₂] at hδ₃ hδ₄ he₂ hd₃
  have hδ₃' : δ₃ = 1 := by rw [hδ₃]; ring
  have hδ₄' : δ₄ = -1 := by rw [hδ₄]; ring
  have hd₃' : d₃ = (q - -1) * d₂ + -1 := by rw [hd₃]; ring
  have he₂' : e₂ = 1 := by rw [he₂]; ring
  have he₄' : e₄ = 1 := by rw [he₄, hδ₄']; ring
  have hstar := eight_ten (a := a) hq he pd₂ (by rw [← hd₃']; exact pd₃) (by
    rw [← hd₃']
    rw [hδ₂, hδ₃', hδ₄', hd₄] at h6
    push_cast at h6 ⊢
    linear_combination h6)
  have hpar' : Odd d₂ := by
    obtain ⟨k, hk⟩ := hpar
    rw [hδ₂] at hk
    exact ⟨k - 1, by omega⟩
  have hint' : ((q - -1) * d₂ + -1) ∣ q ^ 3 * a := by
    rw [← hd₃']
    rw [hδ₃'] at hint₃
    have : q ^ 2 * a * (-(-1) * q * 1) = q ^ 3 * a := by ring
    rwa [this] at hint₃
  obtain ⟨hd₂', ha'⟩ := eight_numth hp hqpm hq he hq8 pd₂ hstar hR
    (by rw [he₂'] at hRo; exact hRo) hpar'
    (by rw [hδ₂, show d₂ + 7 * -1 = d₂ - 7 by ring] at hsyl; exact hsyl) hint'
  have hd₂'' : d₂ = q ^ 2 - q + 1 := by rw [hd₂']; ring
  have hd₃q : d₃ = q ^ 3 := by rw [hd₃', hd₂']; ring
  have hd₄q : d₄ = q * (q ^ 2 - q + 1) := by rw [hd₄, hd₂'']
  have he₃ : e₃ = 1 := by rw [← hσ, hδ₃']
  refine ⟨hδ₂, hδ₃', hδ₄', he₂', he₃, he₄', hd₂'', hd₃q, hd₄q, ?_, by rw [ha']; ring⟩
  rw [he₂', he₃, he₄', hd₂'', hd₃q, hd₄q] at R2
  linarith

theorem two_roots {q m f₅ f₆ : ℤ} (hq : q = 3 * m ^ 2) (hsum : f₅ + f₆ = -q * (q - 1))
    (hprod : 12 * f₅ * f₆ = -q * (q ^ 2 - q + 1) * (q - 1) ^ 2) :
    (2 * f₅ = (q - 1) * m * (q + 1 - 3 * m) ∧ 2 * f₆ = -((q - 1) * m * (q + 1 + 3 * m))) ∨
      (2 * f₆ = (q - 1) * m * (q + 1 - 3 * m) ∧ 2 * f₅ = -((q - 1) * m * (q + 1 + 3 * m))) := by
  have hsq : (f₅ - f₆) ^ 2 = ((q - 1) * (q + 1) * m) ^ 2 := by
    have h1 : (f₅ - f₆) ^ 2 = (f₅ + f₆) ^ 2 - 4 * (f₅ * f₆) := by ring
    have h2 : 3 * (4 * (f₅ * f₆)) = -q * (q ^ 2 - q + 1) * (q - 1) ^ 2 := by
      linear_combination hprod
    have h3 : 3 * (f₅ - f₆) ^ 2 = 3 * ((q - 1) * (q + 1) * m) ^ 2 := by
      rw [h1, hsum]
      have : 3 * ((-q * (q - 1)) ^ 2 - 4 * (f₅ * f₆)) =
          3 * q ^ 2 * (q - 1) ^ 2 + q * (q ^ 2 - q + 1) * (q - 1) ^ 2 := by
        linear_combination (-1 : ℤ) * h2
      rw [this, hq]
      ring
    linarith
  subst hq
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · left
    exact ⟨by linear_combination hsum + h, by linear_combination hsum - h⟩
  · right
    exact ⟨by linear_combination hsum - h, by linear_combination hsum + h⟩

end CFSG.Walter.WardLocal
