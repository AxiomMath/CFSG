module

public import CFSG.RankThree.PartTwo.Sec21.FF79KFactsZ

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

set_option synthInstance.maxSize 20000 in
set_option synthInstance.maxHeartbeats 1000000 in
private theorem l3NonAbPoly :
    ∀ a b c d e f g h i : ZMod 2,
      ((a * a + b * d + c * g = 1) ∧
        (a * b + b * e + c * h = 0) ∧
        (a * c + b * f + c * i = 0) ∧
        (d * a + e * d + f * g = 0) ∧
        (d * b + e * e + f * h = 1) ∧
        (d * c + e * f + f * i = 0) ∧
        (g * a + h * d + i * g = 0) ∧
        (g * b + h * e + i * h = 0) ∧
        (g * c + h * f + i * i = 1)) →
      ¬ (a = 1 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 1 ∧ f = 0 ∧ g = 0 ∧ h = 0 ∧ i = 1) →
      ∃ p q r t u v w x z : ZMod 2,
      ((p * p + q * t + r * w = a) ∧
        (p * q + q * u + r * x = b) ∧
        (p * r + q * v + r * z = c) ∧
        (t * p + u * t + v * w = d) ∧
        (t * q + u * u + v * x = e) ∧
        (t * r + u * v + v * z = f) ∧
        (w * p + x * t + z * w = g) ∧
        (w * q + x * u + z * x = h) ∧
        (w * r + x * v + z * z = i)) ∧
      (p * u * z - p * v * x - q * t * z + q * v * w + r * t * x - r * u * w = 1) ∧
      ((p * a + q * d + r * g = a * p + b * t + c * w) ∧
        (p * b + q * e + r * h = a * q + b * u + c * x) ∧
        (p * c + q * f + r * i = a * r + b * v + c * z) ∧
        (t * a + u * d + v * g = d * p + e * t + f * w) ∧
        (t * b + u * e + v * h = d * q + e * u + f * x) ∧
        (t * c + u * f + v * i = d * r + e * v + f * z) ∧
        (w * a + x * d + z * g = g * p + h * t + i * w) ∧
        (w * b + x * e + z * h = g * q + h * u + i * x) ∧
        (w * c + x * f + z * i = g * r + h * v + i * z)) ∧
      ∃ p2 q2 r2 t2 u2 v2 w2 x2 z2 : ZMod 2,
      ((p2 * p2 + q2 * t2 + r2 * w2 = 1) ∧
        (p2 * q2 + q2 * u2 + r2 * x2 = 0) ∧
        (p2 * r2 + q2 * v2 + r2 * z2 = 0) ∧
        (t2 * p2 + u2 * t2 + v2 * w2 = 0) ∧
        (t2 * q2 + u2 * u2 + v2 * x2 = 1) ∧
        (t2 * r2 + u2 * v2 + v2 * z2 = 0) ∧
        (w2 * p2 + x2 * t2 + z2 * w2 = 0) ∧
        (w2 * q2 + x2 * u2 + z2 * x2 = 0) ∧
        (w2 * r2 + x2 * v2 + z2 * z2 = 1)) ∧
      (p2 * u2 * z2 - p2 * v2 * x2 - q2 * t2 * z2 + q2 * v2 * w2 + r2 * t2 * x2 -
        r2 * u2 * w2 = 1) ∧
      ((p2 * a + q2 * d + r2 * g = a * p2 + b * t2 + c * w2) ∧
        (p2 * b + q2 * e + r2 * h = a * q2 + b * u2 + c * x2) ∧
        (p2 * c + q2 * f + r2 * i = a * r2 + b * v2 + c * z2) ∧
        (t2 * a + u2 * d + v2 * g = d * p2 + e * t2 + f * w2) ∧
        (t2 * b + u2 * e + v2 * h = d * q2 + e * u2 + f * x2) ∧
        (t2 * c + u2 * f + v2 * i = d * r2 + e * v2 + f * z2) ∧
        (w2 * a + x2 * d + z2 * g = g * p2 + h * t2 + i * w2) ∧
        (w2 * b + x2 * e + z2 * h = g * q2 + h * u2 + i * x2) ∧
        (w2 * c + x2 * f + z2 * i = g * r2 + h * v2 + i * z2)) ∧
      ¬ ((p * p2 + q * t2 + r * w2 = p2 * p + q2 * t + r2 * w) ∧
        (p * q2 + q * u2 + r * x2 = p2 * q + q2 * u + r2 * x) ∧
        (p * r2 + q * v2 + r * z2 = p2 * r + q2 * v + r2 * z) ∧
        (t * p2 + u * t2 + v * w2 = t2 * p + u2 * t + v2 * w) ∧
        (t * q2 + u * u2 + v * x2 = t2 * q + u2 * u + v2 * x) ∧
        (t * r2 + u * v2 + v * z2 = t2 * r + u2 * v + v2 * z) ∧
        (w * p2 + x * t2 + z * w2 = w2 * p + x2 * t + z2 * w) ∧
        (w * q2 + x * u2 + z * x2 = w2 * q + x2 * u + z2 * x) ∧
        (w * r2 + x * v2 + z * z2 = w2 * r + x2 * v + z2 * z)) := by
  decide +kernel

private def mk3 (a b c d e f g h i : ZMod 2) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  !![a, b, c; d, e, f; g, h, i]

private theorem mk3_mul (a b c d e f g h i p q r t u v w x z : ZMod 2) :
    mk3 a b c d e f g h i * mk3 p q r t u v w x z =
      mk3 (a * p + b * t + c * w) (a * q + b * u + c * x) (a * r + b * v + c * z)
        (d * p + e * t + f * w) (d * q + e * u + f * x) (d * r + e * v + f * z)
        (g * p + h * t + i * w) (g * q + h * u + i * x) (g * r + h * v + i * z) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mk3, Matrix.mul_apply, Fin.sum_univ_three]

private theorem mk3_det (a b c d e f g h i : ZMod 2) :
    (mk3 a b c d e f g h i).det = a * e * i - a * f * h - b * d * i + b * f * g + c * d * h
      - c * e * g := by
  simp [mk3, Matrix.det_fin_three]

private theorem mk3_inj {a b c d e f g h i p q r t u v w x z : ZMod 2} :
    mk3 a b c d e f g h i = mk3 p q r t u v w x z ↔
      (a = p ∧ b = q ∧ c = r ∧ d = t ∧ e = u ∧ f = v ∧ g = w ∧ h = x ∧ i = z) := by
  constructor
  · intro h
    have e := fun i j => congrFun (congrFun h i) j
    exact ⟨by simpa [mk3] using e 0 0, by simpa [mk3] using e 0 1, by simpa [mk3] using e 0 2,
      by simpa [mk3] using e 1 0, by simpa [mk3] using e 1 1, by simpa [mk3] using e 1 2,
      by simpa [mk3] using e 2 0, by simpa [mk3] using e 2 1, by simpa [mk3] using e 2 2⟩
  · rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl

private theorem mk3_eta (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    A = mk3 (A 0 0) (A 0 1) (A 0 2) (A 1 0) (A 1 1) (A 1 2) (A 2 0) (A 2 1) (A 2 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mk3]

private theorem mk3_one : (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) = mk3 1 0 0 0 1 0 0 0 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mk3]

private theorem unit_det_one {a b c d e f g h i : ZMod 2}
    (hd : a * e * i - a * f * h - b * d * i + b * f * g + c * d * h - c * e * g = 1) :
    IsUnit (mk3 a b c d e f g h i).det := by
  rw [mk3_det, hd]; exact isUnit_one

theorem ff79KCentL3NonAb_holds : FF79KCentL3NonAb := by
  intro s hs
  have hs2 : s ^ 2 = 1 := by
    have := pow_orderOf_eq_one s
    rwa [hs] at this
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hs
    omega
  set S : Matrix (Fin 3) (Fin 3) (ZMod 2) := (s : Matrix (Fin 3) (Fin 3) (ZMod 2)) with hS
  have h1 : S * S = 1 := by
    have := congrArg Units.val hs2
    simpa [hS, pow_two] using this
  have h2 : S ≠ 1 := by
    intro h
    exact hs1 (Units.ext h)
  rw [mk3_eta S, mk3_mul, mk3_one, mk3_inj] at h1
  have h2' : ¬ (S 0 0 = 1 ∧ S 0 1 = 0 ∧ S 0 2 = 0 ∧ S 1 0 = 0 ∧ S 1 1 = 1 ∧ S 1 2 = 0 ∧
      S 2 0 = 0 ∧ S 2 1 = 0 ∧ S 2 2 = 1) := by
    intro h
    apply h2
    rw [mk3_eta S, mk3_one, mk3_inj]
    exact h
  obtain ⟨p, q, r, t, u, v, w, x, z, hsq1, hdet1, hc1, p2, q2, r2, t2, u2, v2, w2, x2, z2,
    hsq2, hdet2, hc2, hnc⟩ := l3NonAbPoly _ _ _ _ _ _ _ _ _ h1 h2'
  let d₁ : GL (Fin 3) (ZMod 2) := Matrix.GeneralLinearGroup.mk'' (mk3 p q r t u v w x z)
    (unit_det_one hdet1)
  let d₂ : GL (Fin 3) (ZMod 2) := Matrix.GeneralLinearGroup.mk'' (mk3 p2 q2 r2 t2 u2 v2 w2 x2 z2)
    (unit_det_one hdet2)
  have e1 : (d₁ : Matrix (Fin 3) (Fin 3) (ZMod 2)) = mk3 p q r t u v w x z := rfl
  have e2 : (d₂ : Matrix (Fin 3) (Fin 3) (ZMod 2)) = mk3 p2 q2 r2 t2 u2 v2 w2 x2 z2 := rfl
  have hd1 : d₁ * d₁ = s := by
    apply Units.ext
    rw [Units.val_mul, e1, mk3_mul, ← hS, mk3_eta S, mk3_inj]
    exact ⟨hsq1.1, hsq1.2.1, hsq1.2.2.1, hsq1.2.2.2.1, hsq1.2.2.2.2.1, hsq1.2.2.2.2.2.1,
      hsq1.2.2.2.2.2.2.1, hsq1.2.2.2.2.2.2.2.1, hsq1.2.2.2.2.2.2.2.2⟩
  have hd2 : d₂ * d₂ = 1 := by
    apply Units.ext
    rw [Units.val_mul, e2, mk3_mul, Units.val_one, mk3_one, mk3_inj]
    exact ⟨hsq2.1, hsq2.2.1, hsq2.2.2.1, hsq2.2.2.2.1, hsq2.2.2.2.2.1, hsq2.2.2.2.2.2.1,
      hsq2.2.2.2.2.2.2.1, hsq2.2.2.2.2.2.2.2.1, hsq2.2.2.2.2.2.2.2.2⟩
  refine ⟨d₁, d₂, ?_, ?_, ?_, ?_, ?_⟩
  · apply Units.ext
    rw [Units.val_mul, Units.val_mul, e1, ← hS, mk3_eta S, mk3_mul, mk3_mul, mk3_inj]
    exact ⟨hc1.1, hc1.2.1, hc1.2.2.1, hc1.2.2.2.1, hc1.2.2.2.2.1, hc1.2.2.2.2.2.1,
      hc1.2.2.2.2.2.2.1, hc1.2.2.2.2.2.2.2.1, hc1.2.2.2.2.2.2.2.2⟩
  · apply Units.ext
    rw [Units.val_mul, Units.val_mul, e2, ← hS, mk3_eta S, mk3_mul, mk3_mul, mk3_inj]
    exact ⟨hc2.1, hc2.2.1, hc2.2.2.1, hc2.2.2.2.1, hc2.2.2.2.2.1, hc2.2.2.2.2.2.1,
      hc2.2.2.2.2.2.2.1, hc2.2.2.2.2.2.2.2.1, hc2.2.2.2.2.2.2.2.2⟩
  · calc d₁ ^ 4 = (d₁ * d₁) * (d₁ * d₁) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = s ^ 2 := by rw [hd1, pow_two]
      _ = 1 := hs2
  · calc d₂ ^ 4 = (d₂ * d₂) * (d₂ * d₂) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := by rw [hd2, mul_one]
  · intro h
    have := congrArg Units.val h
    rw [Units.val_mul, Units.val_mul, e1, e2, mk3_mul, mk3_mul, mk3_inj] at this
    exact hnc this

end CFSG.RankThree.PartTwo.Sec21.FF79
