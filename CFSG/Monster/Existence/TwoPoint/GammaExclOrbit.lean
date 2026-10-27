module

public import CFSG.Monster.Existence.TwoPoint.GammaExcl

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

@[expose] noncomputable def gxCand (j : ℕ) (ε : Bool) : MGriess :=
  if ε then fiBeta * deltaHat j * fiBeta else deltaHat j

theorem gx_inv_comm {k a : MGriess} (hk : k * a = a * k) : k⁻¹ * a = a * k⁻¹ := by
  calc k⁻¹ * a = k⁻¹ * (a * k) * k⁻¹ := by group
    _ = k⁻¹ * (k * a) * k⁻¹ := by rw [hk]
    _ = a * k⁻¹ := by group

theorem gx_conj_by_comm {k a x : MGriess} (hk : k * a = a * k) :
    a * (k * x * k⁻¹) * a = k * (a * x * a) * k⁻¹ := by
  calc a * (k * x * k⁻¹) * a = (a * k) * x * (k⁻¹ * a) := by simp only [mul_assoc]
    _ = (k * a) * x * (a * k⁻¹) := by rw [← hk, gx_inv_comm hk]
    _ = k * (a * x * a) * k⁻¹ := by simp only [mul_assoc]

theorem gx_mul_conj_comm {k a y : MGriess} (hk : k * a = a * k) :
    a * (k * y * k⁻¹) = k * (a * y) * k⁻¹ := by
  calc a * (k * y * k⁻¹) = (a * k) * y * k⁻¹ := by simp only [mul_assoc]
    _ = (k * a) * y * k⁻¹ := by rw [← hk]
    _ = k * (a * y) * k⁻¹ := by simp only [mul_assoc]

theorem gx_comm_betaPrime {k : MGriess} (hkα : k * fiAlpha = fiAlpha * k)
    (hkβ : k * fiBeta = fiBeta * k) : k * betaPrime = betaPrime * k := by
  unfold betaPrime
  calc k * (fiAlpha * fiBeta * fiAlpha) = (k * fiAlpha) * fiBeta * fiAlpha := by
        simp only [mul_assoc]
    _ = fiAlpha * (k * fiBeta) * fiAlpha := by rw [hkα]; simp only [mul_assoc]
    _ = fiAlpha * fiBeta * (k * fiAlpha) := by rw [hkβ]; simp only [mul_assoc]
    _ = fiAlpha * fiBeta * fiAlpha * k := by rw [hkα]; simp only [mul_assoc]

theorem gx_conj_commute {k x y : MGriess} (hk : k * y = y * k) (h : x * y = y * x) :
    (k * x * k⁻¹) * y = y * (k * x * k⁻¹) := by
  have hk' := gx_inv_comm hk
  calc k * x * k⁻¹ * y = k * x * (k⁻¹ * y) := by simp only [mul_assoc]
    _ = k * x * (y * k⁻¹) := by rw [hk']
    _ = k * (x * y) * k⁻¹ := by simp only [mul_assoc]
    _ = k * (y * x) * k⁻¹ := by rw [h]
    _ = (k * y) * x * k⁻¹ := by simp only [mul_assoc]
    _ = (y * k) * x * k⁻¹ := by rw [hk]
    _ = y * (k * x * k⁻¹) := by simp only [mul_assoc]

theorem gx_orbit_cases
    {j : ℕ} (hj : j < 23) (ε : Bool) {k : MGriess}
    (hkα : k * fiAlpha = fiAlpha * k) (hkβ : k * fiBeta = fiBeta * k)
    (hc : (k * gxCand j ε * k⁻¹) * betaPrime = betaPrime * (k * gxCand j ε * k⁻¹)) :
    (j = 1 ∧ ε = false) ∨ (j = 0 ∧ ε = true) ∨ (j = 9 ∧ ε = true) := by
  have hkb := gx_comm_betaPrime hkα hkβ
  have hc' : gxCand j ε * betaPrime = betaPrime * gxCand j ε := by
    have h1 := gx_conj_commute (gx_inv_comm hkb) hc
    have e : k⁻¹ * (k * gxCand j ε * k⁻¹) * k⁻¹⁻¹ = gxCand j ε := by group
    rwa [e] at h1
  cases ε
  · have h0 : deltaHat j * betaPrime = betaPrime * deltaHat j := by simpa [gxCand] using hc'
    rcases (by omega : j = 0 ∨ j = 1 ∨ 2 ≤ j) with h | h | h
    · subst h
      rw [deltaHat_zero] at h0
      exact absurd h0 fiAlpha_not_commute_betaPrime
    · exact Or.inl ⟨h, rfl⟩
    · exact absurd h0 (deltaHat_not_commute_betaPrime h hj)
  · have h0 : (fiBeta * deltaHat j * fiBeta) * betaPrime =
        betaPrime * (fiBeta * deltaHat j * fiBeta) := by simpa [gxCand] using hc'
    have hα : deltaHat j * fiAlpha = fiAlpha * deltaHat j := by
      by_contra hne
      exact fiBeta_conj_not_commute_betaPrime hne h0
    rcases (by omega : j = 0 ∨ 1 ≤ j) with h | h
    · exact Or.inr (Or.inl ⟨h, rfl⟩)
    · by_cases h9 : j = 9
      · exact Or.inr (Or.inr ⟨h9, rfl⟩)
      · exact absurd hα (deltaHat_not_commute_alpha h hj h9)

theorem gx_star_gamma
    {k : MGriess} (hkα : k * fiAlpha = fiAlpha * k) :
    fiAlpha * (k * deltaHat 1 * k⁻¹) * fiAlpha = k * gammaZero * k⁻¹ := by
  have hα := fiAlpha_mul_self
  have hA : fiAlpha * (fiAlpha * gammaZero * fiAlpha) * fiAlpha = gammaZero := by
    calc fiAlpha * (fiAlpha * gammaZero * fiAlpha) * fiAlpha
        = (fiAlpha * fiAlpha) * gammaZero * (fiAlpha * fiAlpha) := by simp only [mul_assoc]
      _ = gammaZero := by rw [hα]; simp
  rw [gx_conj_by_comm hkα, deltaHat_one, hA]

theorem gx_twin_not_isConj
    {k : MGriess} (hkα : k * fiAlpha = fiAlpha * k)
    (hkβ : k * fiBeta = fiBeta * k) :
    ¬ IsConj tGriess (fiBeta * (fiAlpha * (k * gxCand 9 true * k⁻¹) * fiAlpha)) := by
  have hX : gxCand 9 true = fiBeta * deltaHat 9 * fiBeta := by simp [gxCand]
  have e : fiBeta * (fiAlpha * (k * gxCand 9 true * k⁻¹) * fiAlpha) =
      k * (fiBeta * (fiAlpha * (fiBeta * deltaHat 9 * fiBeta) * fiAlpha)) * k⁻¹ := by
    rw [hX, gx_conj_by_comm hkα, gx_mul_conj_comm hkβ]
  rw [e]
  intro h
  exact not_isConj_tGriess_fiBeta_mul_twisted_gamma_nine
    (h.trans (isConj_iff.2 ⟨k⁻¹, by group⟩))

theorem gx_root_twisted_not_isConj
    {k : MGriess} (hkα : k * fiAlpha = fiAlpha * k)
    (hkβ : k * fiBeta = fiBeta * k) :
    ¬ IsConj tGriess (fiBeta * (fiAlpha * (k * gxCand 0 true * k⁻¹) * fiAlpha)) := by
  have hαl : ∀ x, fiAlpha * (fiAlpha * x) = x := fun x => by
    rw [← mul_assoc, fiAlpha_mul_self, one_mul]
  have hc1 : k * (fiBeta * fiAlpha * fiBeta) * k⁻¹ = fiBeta * fiAlpha * fiBeta := by
    calc k * (fiBeta * fiAlpha * fiBeta) * k⁻¹ = (k * fiBeta) * fiAlpha * fiBeta * k⁻¹ := by
          simp only [mul_assoc]
      _ = fiBeta * (k * fiAlpha) * fiBeta * k⁻¹ := by rw [hkβ]; simp only [mul_assoc]
      _ = fiBeta * fiAlpha * (k * fiBeta) * k⁻¹ := by rw [hkα]; simp only [mul_assoc]
      _ = fiBeta * fiAlpha * fiBeta * (k * k⁻¹) := by rw [hkβ]; simp only [mul_assoc]
      _ = fiBeta * fiAlpha * fiBeta := by simp
  have hγ : fiAlpha * (fiBeta * fiAlpha * fiBeta) * fiAlpha = fiBeta := by
    calc fiAlpha * (fiBeta * fiAlpha * fiBeta) * fiAlpha
        = fiAlpha * (fiAlpha * fiBeta * fiAlpha) * fiAlpha := by
          rw [fiBeta_mul_fiAlpha_mul_fiBeta]
      _ = fiBeta := by
          simp only [mul_assoc]
          rw [fiAlpha_mul_self, mul_one, hαl]
  have e : fiBeta * (fiAlpha * (k * gxCand 0 true * k⁻¹) * fiAlpha) = 1 := by
    have hX : gxCand 0 true = fiBeta * fiAlpha * fiBeta := by simp [gxCand, deltaHat_zero]
    rw [hX, hc1, hγ, fiBeta_mul_self]
  rw [e]
  intro h
  have h1 : tGriess = 1 := isConj_one_left.1 h
  have h2 := orderOf_tGriess
  rw [h1, orderOf_one] at h2
  omega

end CFSG.Monster.Existence
