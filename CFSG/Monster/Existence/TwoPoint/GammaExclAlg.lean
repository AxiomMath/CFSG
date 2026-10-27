module

public import CFSG.Monster.Existence.TwoPoint.GammaExclNode1

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

theorem deltaHat_mul_self
    (j : ℕ) : deltaHat j * deltaHat j = 1 := by
  unfold deltaHat
  calc xHat j * fiAlpha * (xHat j)⁻¹ * (xHat j * fiAlpha * (xHat j)⁻¹)
      = xHat j * (fiAlpha * fiAlpha) * (xHat j)⁻¹ := by group
    _ = 1 := by rw [fiAlpha_mul_self]; group

theorem fiBeta_mul_fiAlpha_mul_fiBeta :
    fiBeta * fiAlpha * fiBeta = fiAlpha * fiBeta * fiAlpha := by
  have hα : fiAlpha⁻¹ = fiAlpha := inv_eq_of_mul_eq_one_right fiAlpha_mul_self
  have hβ : fiBeta⁻¹ = fiBeta := inv_eq_of_mul_eq_one_right fiBeta_mul_self
  have h3 : fiAlpha * fiBeta * fiAlpha * (fiBeta * fiAlpha * fiBeta) = 1 := by
    have := fiAlpha_mul_fiBeta_pow_three
    simpa [pow_succ, mul_assoc] using this
  have h4 : fiBeta * fiAlpha * fiBeta = (fiAlpha * fiBeta * fiAlpha)⁻¹ :=
    eq_inv_of_mul_eq_one_right h3
  rw [mul_inv_rev, mul_inv_rev, hα, hβ] at h4
  rw [h4]
  simp only [mul_assoc]

theorem betaPrime_mul_self :
    betaPrime * betaPrime = 1 := by
  unfold betaPrime
  have hα : ∀ x, fiAlpha * (fiAlpha * x) = x := fun x => by
    rw [← mul_assoc, fiAlpha_mul_self, one_mul]
  have hβ : ∀ x, fiBeta * (fiBeta * x) = x := fun x => by
    rw [← mul_assoc, fiBeta_mul_self, one_mul]
  simp only [mul_assoc]
  rw [hα (fiBeta * fiAlpha), hβ fiAlpha, fiAlpha_mul_self]

theorem fiBeta_mul_betaPrime_mul_fiBeta :
    fiBeta * betaPrime * fiBeta = fiAlpha := by
  unfold betaPrime
  have hα : ∀ x, fiAlpha * (fiAlpha * x) = x := fun x => by
    rw [← mul_assoc, fiAlpha_mul_self, one_mul]
  calc fiBeta * (fiAlpha * fiBeta * fiAlpha) * fiBeta
      = (fiBeta * fiAlpha * fiBeta) * (fiAlpha * fiBeta) := by simp only [mul_assoc]
    _ = (fiAlpha * fiBeta * fiAlpha) * (fiAlpha * fiBeta) := by
        rw [fiBeta_mul_fiAlpha_mul_fiBeta]
    _ = fiAlpha := by
        simp only [mul_assoc]
        rw [hα fiBeta, fiBeta_mul_self, mul_one]

theorem gx_conj_comm {b x y : MGriess} (hb : b * b = 1) (h : x * y = y * x) :
    b * x * b * (b * y * b) = b * y * b * (b * x * b) := by
  calc b * x * b * (b * y * b) = b * (x * y) * b := by
        calc b * x * b * (b * y * b) = b * x * (b * b) * y * b := by simp only [mul_assoc]
          _ = b * (x * y) * b := by rw [hb, mul_one]; simp only [mul_assoc]
    _ = b * (y * x) * b := by rw [h]
    _ = b * y * b * (b * x * b) := by
        calc b * (y * x) * b = b * y * (b * b) * x * b := by rw [hb, mul_one]; simp only [mul_assoc]
          _ = b * y * b * (b * x * b) := by simp only [mul_assoc]

theorem fiBeta_conj_not_commute_betaPrime
    {δ : MGriess} (h : δ * fiAlpha ≠ fiAlpha * δ) :
    (fiBeta * δ * fiBeta) * betaPrime ≠ betaPrime * (fiBeta * δ * fiBeta) := by
  intro hc
  apply h
  have hl : ∀ x, fiBeta * (fiBeta * x) = x := fun x => by
    rw [← mul_assoc, fiBeta_mul_self, one_mul]
  have hδ : fiBeta * (fiBeta * δ * fiBeta) * fiBeta = δ := by
    simp only [mul_assoc]
    rw [fiBeta_mul_self, mul_one, hl]
  have key := gx_conj_comm fiBeta_mul_self hc
  rwa [hδ, fiBeta_mul_betaPrime_mul_fiBeta] at key

theorem gx_mul_eq_one_of_commute {a b : MGriess} (ha : a * a = 1) (hb : b * b = 1)
    (hc : a * b = b * a) (h3 : (a * b) ^ 3 = 1) : a * b = 1 := by
  have h2 : (a * b) * (a * b) = 1 := by
    calc (a * b) * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
      _ = a * (a * b) * b := by rw [← hc]
      _ = (a * a) * (b * b) := by simp only [mul_assoc]
      _ = 1 := by rw [ha, hb, one_mul]
  have h3' : (a * b) ^ 3 = a * b := by rw [pow_succ, sq, h2, one_mul]
  rw [← h3']
  exact h3

theorem deltaHat_zero : deltaHat 0 = fiAlpha := by
  unfold deltaHat
  rw [xHat_zero]
  group

theorem fiAlpha_mul_betaPrime_mul_fiAlpha :
    fiAlpha * betaPrime * fiAlpha = fiBeta := by
  unfold betaPrime
  have hα : ∀ x, fiAlpha * (fiAlpha * x) = x := fun x => by
    rw [← mul_assoc, fiAlpha_mul_self, one_mul]
  simp only [mul_assoc]
  rw [fiAlpha_mul_self, mul_one, hα]

theorem fiBeta_mul_fiAlpha_mul_fiBeta_eq :
    fiBeta * fiAlpha * fiBeta = betaPrime :=
  fiBeta_mul_fiAlpha_mul_fiBeta

theorem fiAlpha_not_commute_betaPrime :
    fiAlpha * betaPrime ≠ betaPrime * fiAlpha := by
  intro h
  unfold betaPrime at h
  have hα : ∀ x, fiAlpha * (fiAlpha * x) = x := fun x => by
    rw [← mul_assoc, fiAlpha_mul_self, one_mul]
  have e1 : fiAlpha * (fiAlpha * fiBeta * fiAlpha) = fiBeta * fiAlpha := by
    simp only [mul_assoc]
    rw [hα]
  have e2 : fiAlpha * fiBeta * fiAlpha * fiAlpha = fiAlpha * fiBeta := by
    simp only [mul_assoc]
    rw [fiAlpha_mul_self, mul_one]
  have hc : fiAlpha * fiBeta = fiBeta * fiAlpha := by
    calc fiAlpha * fiBeta = fiAlpha * fiBeta * fiAlpha * fiAlpha := e2.symm
      _ = fiAlpha * (fiAlpha * fiBeta * fiAlpha) := h.symm
      _ = fiBeta * fiAlpha := e1
  exact fiAlpha_mul_fiBeta_ne_one
    (gx_mul_eq_one_of_commute fiAlpha_mul_self fiBeta_mul_self hc fiAlpha_mul_fiBeta_pow_three)

theorem gxW_mul_fiAlpha
    (h : List ℕ) : gxW h * fiAlpha = fiAlpha * gxW h := by
  induction h with
  | nil => simp [gxW]
  | cons c h ih =>
    have e : gxW (c :: h) = fiE (gxSigma c) * gxW h := by simp [gxW]
    rw [e, mul_assoc, ih, ← mul_assoc, fiE_commute_alpha (gxSigma_lt c), mul_assoc]

theorem gxT_conj_fiAlpha
    (j : ℕ) : gxT j * fiAlpha * (gxT j)⁻¹ = fiAlpha * gxT j * fiAlpha := by
  unfold gxT
  set W := gxW (gxWord j) with hW
  have hc : W * fiAlpha = fiAlpha * W := gxW_mul_fiAlpha _
  have hc2 : W⁻¹ * fiAlpha = fiAlpha * W⁻¹ := by
    calc W⁻¹ * fiAlpha = W⁻¹ * (fiAlpha * W) * W⁻¹ := by group
      _ = W⁻¹ * (W * fiAlpha) * W⁻¹ := by rw [hc]
      _ = fiAlpha * W⁻¹ := by group
  have hγ : gammaZero⁻¹ = gammaZero := inv_eq_of_mul_eq_one_right gammaZero_mul_self
  have hb := gammaZero_mul_fiAlpha_mul_gammaZero
  calc W * gammaZero * W⁻¹ * fiAlpha * (W * gammaZero * W⁻¹)⁻¹
      = W * gammaZero * (W⁻¹ * fiAlpha * W) * gammaZero⁻¹ * W⁻¹ := by group
    _ = W * (gammaZero * fiAlpha * gammaZero) * W⁻¹ := by
        have : W⁻¹ * fiAlpha * W = fiAlpha := by
          calc W⁻¹ * fiAlpha * W = W⁻¹ * (fiAlpha * W) := by rw [mul_assoc]
            _ = W⁻¹ * (W * fiAlpha) := by rw [hc]
            _ = fiAlpha := by group
        rw [this, hγ]
        simp only [mul_assoc]
    _ = W * (fiAlpha * gammaZero * fiAlpha) * W⁻¹ := by rw [hb]
    _ = fiAlpha * (W * gammaZero * W⁻¹) * fiAlpha := by
        calc W * (fiAlpha * gammaZero * fiAlpha) * W⁻¹
            = (W * fiAlpha) * gammaZero * (fiAlpha * W⁻¹) := by simp only [mul_assoc]
          _ = (fiAlpha * W) * gammaZero * (W⁻¹ * fiAlpha) := by rw [hc, hc2]
          _ = fiAlpha * (W * gammaZero * W⁻¹) * fiAlpha := by simp only [mul_assoc]

theorem deltaHat_eq
    {j : ℕ} (h0 : 0 < j) (h23 : j < 23) :
    deltaHat j = xHat (gxParent j) * (fiAlpha * gxT j * fiAlpha) * (xHat (gxParent j))⁻¹ := by
  unfold deltaHat
  rw [xHat_succ h0 h23, ← gxT_conj_fiAlpha j]
  group

theorem fiAlpha_mul_deltaHat_nine :
    fiAlpha * deltaHat 9 = (gammaZero * fiAlpha) * xHat 9 * (gammaZero * fiAlpha)⁻¹ := by
  have e : gxParent 9 = 1 := by decide
  have hα : fiAlpha⁻¹ = fiAlpha := inv_eq_of_mul_eq_one_right fiAlpha_mul_self
  have hγ : gammaZero⁻¹ = gammaZero := inv_eq_of_mul_eq_one_right gammaZero_mul_self
  have hb := gammaZero_mul_fiAlpha_mul_gammaZero
  rw [deltaHat_eq (by omega) (by omega), e, xHat_one, mul_inv_rev, hα, hγ, xHat_succ (by omega)
    (by omega), e, xHat_one]
  calc fiAlpha * (gammaZero * (fiAlpha * gxT 9 * fiAlpha) * gammaZero)
      = (fiAlpha * gammaZero * fiAlpha) * gxT 9 * fiAlpha * gammaZero := by simp only [mul_assoc]
    _ = (gammaZero * fiAlpha * gammaZero) * gxT 9 * fiAlpha * gammaZero := by rw [hb]
    _ = gammaZero * fiAlpha * (gammaZero * gxT 9) * (fiAlpha * gammaZero) := by
        simp only [mul_assoc]

theorem fiBeta_mul_twisted_gamma_nine :
    fiBeta * (fiAlpha * (fiBeta * deltaHat 9 * fiBeta) * fiAlpha) =
      (fiAlpha * fiBeta) * (fiAlpha * deltaHat 9) * (fiAlpha * fiBeta)⁻¹ := by
  have hα : fiAlpha⁻¹ = fiAlpha := inv_eq_of_mul_eq_one_right fiAlpha_mul_self
  have hβ : fiBeta⁻¹ = fiBeta := inv_eq_of_mul_eq_one_right fiBeta_mul_self
  have hb := fiBeta_mul_fiAlpha_mul_fiBeta
  rw [mul_inv_rev, hα, hβ]
  calc fiBeta * (fiAlpha * (fiBeta * deltaHat 9 * fiBeta) * fiAlpha)
      = (fiBeta * fiAlpha * fiBeta) * deltaHat 9 * (fiBeta * fiAlpha) := by simp only [mul_assoc]
    _ = (fiAlpha * fiBeta * fiAlpha) * deltaHat 9 * (fiBeta * fiAlpha) := by rw [hb]
    _ = (fiAlpha * fiBeta) * (fiAlpha * deltaHat 9) * (fiBeta * fiAlpha) := by
        simp only [mul_assoc]

end CFSG.Monster.Existence
