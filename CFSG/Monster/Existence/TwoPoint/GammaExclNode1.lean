module

public import CFSG.Monster.Existence.TwoPoint.Fi23
public import CFSG.Monster.Existence.TwoPoint.Fi23S4
public import CFSG.Monster.Existence.TwoPoint.GammaExclDefBase

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

theorem gammaZero_mul_fiAlpha_mul_gammaZero :
    gammaZero * fiAlpha * gammaZero = fiAlpha * gammaZero * fiAlpha := by
  have hα : fiAlpha⁻¹ = fiAlpha := inv_eq_of_mul_eq_one_right fiAlpha_mul_self
  have hγ : gammaZero⁻¹ = gammaZero := inv_eq_of_mul_eq_one_right gammaZero_mul_self
  have h3 : fiAlpha * gammaZero * fiAlpha * (gammaZero * fiAlpha * gammaZero) = 1 := by
    have := fiAlpha_mul_gammaZero_pow_three
    simpa [pow_succ, mul_assoc] using this
  have h4 : gammaZero * fiAlpha * gammaZero = (fiAlpha * gammaZero * fiAlpha)⁻¹ :=
    eq_inv_of_mul_eq_one_right h3
  rw [mul_inv_rev, mul_inv_rev, hα, hγ] at h4
  rw [h4]
  simp only [mul_assoc]

theorem deltaHat_one :
    deltaHat 1 = fiAlpha * gammaZero * fiAlpha := by
  have hγ : gammaZero⁻¹ = gammaZero := inv_eq_of_mul_eq_one_right gammaZero_mul_self
  unfold deltaHat
  rw [xHat_one, hγ]
  exact gammaZero_mul_fiAlpha_mul_gammaZero

theorem deltaHat_one_mul_betaPrime :
    deltaHat 1 * betaPrime = betaPrime * deltaHat 1 := by
  rw [deltaHat_one, betaPrime]
  have hα := fiAlpha_mul_self
  have hc := fiBeta_commute_gammaZero
  calc fiAlpha * gammaZero * fiAlpha * (fiAlpha * fiBeta * fiAlpha)
      = fiAlpha * gammaZero * (fiAlpha * fiAlpha) * fiBeta * fiAlpha := by simp only [mul_assoc]
    _ = fiAlpha * (gammaZero * fiBeta) * fiAlpha := by rw [hα, mul_one]; simp only [mul_assoc]
    _ = fiAlpha * (fiBeta * gammaZero) * fiAlpha := by rw [← hc]
    _ = fiAlpha * fiBeta * (fiAlpha * fiAlpha) * gammaZero * fiAlpha := by
        rw [hα, mul_one]; simp only [mul_assoc]
    _ = fiAlpha * fiBeta * fiAlpha * (fiAlpha * gammaZero * fiAlpha) := by simp only [mul_assoc]

theorem deltaHat_one_not_commute_alpha :
    deltaHat 1 * fiAlpha ≠ fiAlpha * deltaHat 1 := by
  intro h
  rw [deltaHat_one] at h
  have hα := fiAlpha_mul_self
  have hγ := gammaZero_mul_self
  have hl : ∀ x, fiAlpha * (fiAlpha * x) = x := fun x => by rw [← mul_assoc, hα, one_mul]
  have hr : ∀ x, x * fiAlpha * fiAlpha = x := fun x => by rw [mul_assoc, hα, mul_one]
  have h1 : fiAlpha * gammaZero = gammaZero * fiAlpha := by
    have e2 : fiAlpha * (fiAlpha * gammaZero * fiAlpha) = gammaZero * fiAlpha := by
      rw [mul_assoc fiAlpha gammaZero fiAlpha]
      exact hl _
    calc fiAlpha * gammaZero = fiAlpha * gammaZero * fiAlpha * fiAlpha := (hr _).symm
      _ = fiAlpha * (fiAlpha * gammaZero * fiAlpha) := h
      _ = gammaZero * fiAlpha := e2
  have h2 : (fiAlpha * gammaZero) * (fiAlpha * gammaZero) = 1 := by
    calc (fiAlpha * gammaZero) * (fiAlpha * gammaZero)
        = fiAlpha * (gammaZero * fiAlpha) * gammaZero := by simp only [mul_assoc]
      _ = fiAlpha * (fiAlpha * gammaZero) * gammaZero := by rw [← h1]
      _ = (fiAlpha * fiAlpha) * (gammaZero * gammaZero) := by simp only [mul_assoc]
      _ = 1 := by rw [hα, hγ, one_mul]
  have h3 : (fiAlpha * gammaZero) ^ 3 = fiAlpha * gammaZero := by
    rw [pow_succ, sq, h2, one_mul]
  exact fiAlpha_mul_gammaZero_ne_one (by rw [← h3]; exact fiAlpha_mul_gammaZero_pow_three)

end CFSG.Monster.Existence
