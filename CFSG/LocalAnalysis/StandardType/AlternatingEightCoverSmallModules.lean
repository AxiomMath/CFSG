module

public import CFSG.LocalAnalysis.StandardType.AlternatingEightCoverElements
public import CFSG.LocalAnalysis.StandardType.OrderFiveSevenSpectrum

public section

namespace CFSG.StandardType

open Matrix

variable {J : Type*} [Group J] [Finite J] {E : Type*} [Field E] [IsAlgClosed E] [CharP E 2]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem map_conj_sq_aux {M : Type*} [Monoid M] (ρ : J →* M) {x y : J} (hxy : y * x * y⁻¹ = x ^ 2) :
    ρ y * ρ x = ρ x ^ 2 * ρ y := by
  have h : y * x = x ^ 2 * y := by
    calc y * x = (y * x * y⁻¹) * y := by group
      _ = x ^ 2 * y := by rw [hxy]
  rw [← map_mul, h, map_mul, map_pow]

theorem IsAlternatingEightCover.map_eq_one_of_card_le_three (hJ : IsAlternatingEightCover J)
    (hι : Fintype.card ι ≤ 3) (ρ : J →* Matrix ι ι E) (g : J) : ρ g = 1 := by
  obtain ⟨x, y, hx, hxy⟩ := hJ.exists_orderOf_five_conj_sq
  have hX : ρ x ^ 5 = 1 := by
    rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one]
  have hY : IsUnit (ρ y) := (Group.isUnit y).map ρ
  have h1 : ρ x = 1 :=
    OrderFiveSeven.eq_one_of_pow_five_of_card_le_three hι hY (map_conj_sq_aux ρ hxy) hX
  exact hJ.map_eq_one_of_map_eq_one (Or.inl hx) ρ h1 g

theorem IsAlternatingEightCover.map_eq_one_of_card_le_five_of_form (hJ : IsAlternatingEightCover J)
    (σ : E ≃+* E) (hσ : ∀ η : E, η ^ 7 = 1 → ∃ k : ℕ, σ η = η ^ 2 ^ k) {G : Matrix ι ι E}
    (hG : IsUnit G) (hι : Fintype.card ι ≤ 5) (ρ : J →* Matrix ι ι E)
    (hρ : ∀ g, (ρ g)ᵀ * G * (ρ g).map σ = G) (g : J) : ρ g = 1 := by
  obtain ⟨x, y, hx, hxy⟩ := hJ.exists_orderOf_seven_conj_sq
  have hX : ρ x ^ 7 = 1 := by
    rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one]
  have hY : IsUnit (ρ y) := (Group.isUnit y).map ρ
  have h1 : ρ x = 1 :=
    OrderFiveSeven.eq_one_of_pow_seven_of_form σ hσ hG hι hY (map_conj_sq_aux ρ hxy) hX (hρ x)
  exact hJ.map_eq_one_of_map_eq_one (Or.inr hx) ρ h1 g

end CFSG.StandardType
