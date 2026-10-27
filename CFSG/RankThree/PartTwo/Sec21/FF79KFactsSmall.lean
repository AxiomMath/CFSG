module

public import CFSG.RankThree.PartTwo.Sec21.FF79KFacts

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

private theorem a5Perm :
    ∀ w g : Equiv.Perm (Fin 5), w ≠ 1 → w ^ 3 = 1 → g * w = w * g →
      Equiv.Perm.sign w = 1 → Equiv.Perm.sign g = 1 → g = 1 ∨ g = w ∨ g = w ^ 2 := by
  decide +kernel

set_option synthInstance.maxSize 20000 in
set_option synthInstance.maxHeartbeats 1000000 in
private theorem l3Poly :
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
      ∀ p q r t u v w x z : ZMod 2,
      ((p * a + q * d + r * g = a * p + b * t + c * w) ∧
        (p * b + q * e + r * h = a * q + b * u + c * x) ∧
        (p * c + q * f + r * i = a * r + b * v + c * z) ∧
        (t * a + u * d + v * g = d * p + e * t + f * w) ∧
        (t * b + u * e + v * h = d * q + e * u + f * x) ∧
        (t * c + u * f + v * i = d * r + e * v + f * z) ∧
        (w * a + x * d + z * g = g * p + h * t + i * w) ∧
        (w * b + x * e + z * h = g * q + h * u + i * x) ∧
        (w * c + x * f + z * i = g * r + h * v + i * z)) →
      (p * u * z - p * v * x - q * t * z + q * v * w + r * t * x - r * u * w = 1) →
      (((p * p + q * t + r * w = 1) ∧
        (p * q + q * u + r * x = 0) ∧
        (p * r + q * v + r * z = 0) ∧
        (t * p + u * t + v * w = 0) ∧
        (t * q + u * u + v * x = 1) ∧
        (t * r + u * v + v * z = 0) ∧
        (w * p + x * t + z * w = 0) ∧
        (w * q + x * u + z * x = 0) ∧
        (w * r + x * v + z * z = 1)) ∨
       ((p * p + q * t + r * w = a) ∧
        (p * q + q * u + r * x = b) ∧
        (p * r + q * v + r * z = c) ∧
        (t * p + u * t + v * w = d) ∧
        (t * q + u * u + v * x = e) ∧
        (t * r + u * v + v * z = f) ∧
        (w * p + x * t + z * w = g) ∧
        (w * q + x * u + z * x = h) ∧
        (w * r + x * v + z * z = i))) := by
  decide +kernel

theorem ff79KCentA5_holds : FF79KCentA5 := by
  intro w g hw hg
  have h3 : orderOf w = 3 := hw
  have hw1 : (w : Equiv.Perm (Fin 5)) ≠ 1 := by
    intro h
    have : w = 1 := Subtype.ext h
    rw [this, orderOf_one] at h3
    omega
  have hw3 : (w : Equiv.Perm (Fin 5)) ^ 3 = 1 := by
    have := pow_orderOf_eq_one w
    rw [h3] at this
    exact congrArg Subtype.val this
  have hc : (g : Equiv.Perm (Fin 5)) * w = w * g := congrArg Subtype.val hg
  have hsw := a5Perm w g hw1 hw3 hc (Equiv.Perm.mem_alternatingGroup.mp w.2)
    (Equiv.Perm.mem_alternatingGroup.mp g.2)
  have hw3' : w ^ 3 = 1 := by
    have := pow_orderOf_eq_one w
    rwa [h3] at this
  rcases hsw with h | h | h
  · have : g = 1 := Subtype.ext h
    rw [this]; exact Subgroup.one_mem _
  · have : g = w := Subtype.ext h
    rw [this]; exact Subgroup.mem_zpowers w
  · have : g = w ^ 2 := Subtype.ext (by simpa using h)
    rw [this]
    exact Subgroup.npow_mem_zpowers w 2

theorem ff79KCentL3_holds : FF79KCentL3 := by
  intro s y hs hy
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs2 : s ^ 2 = 1 := by
    have := pow_orderOf_eq_one s
    rwa [hs] at this
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hs
    omega
  set S : Matrix (Fin 3) (Fin 3) (ZMod 2) := (s : Matrix (Fin 3) (Fin 3) (ZMod 2)) with hS
  set Y : Matrix (Fin 3) (Fin 3) (ZMod 2) := (y : Matrix (Fin 3) (Fin 3) (ZMod 2)) with hY
  have h1 : S * S = 1 := by
    have := congrArg Units.val hs2
    simpa [hS, pow_two] using this
  have h2 : S ≠ 1 := by
    intro h
    exact hs1 (Units.ext h)
  have h3 : Y * S = S * Y := by
    have := congrArg Units.val hy
    simpa [hS, hY] using this
  have h4 : Y.det = 1 := by
    have hu := (Matrix.GeneralLinearGroup.det y).isUnit
    have : IsUnit Y.det := by simpa [hY] using hu
    exact (by decide : ∀ a : ZMod 2, IsUnit a → a = 1) _ this
  have e1 : ∀ i j, (S * S) i j = (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j :=
    fun i j => by rw [h1]
  have e3 : ∀ i j, (Y * S) i j = (S * Y) i j := fun i j => by rw [h3]
  have d4 := h4
  rw [Matrix.det_fin_three] at d4
  have h2' : ¬ (S 0 0 = 1 ∧ S 0 1 = 0 ∧ S 0 2 = 0 ∧ S 1 0 = 0 ∧ S 1 1 = 1 ∧ S 1 2 = 0 ∧
      S 2 0 = 0 ∧ S 2 1 = 0 ∧ S 2 2 = 1) := by
    rintro ⟨c00, c01, c02, c10, c11, c12, c20, c21, c22⟩
    apply h2
    ext i j
    fin_cases i <;> fin_cases j <;> simpa [Matrix.one_apply]
  have key := l3Poly (S 0 0) (S 0 1) (S 0 2) (S 1 0) (S 1 1) (S 1 2) (S 2 0) (S 2 1) (S 2 2)
    ⟨by simpa [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] using e1 0 0,
      by simpa [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] using e1 0 1,
      by simpa [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] using e1 0 2,
      by simpa [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] using e1 1 0,
      by simpa [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] using e1 1 1,
      by simpa [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] using e1 1 2,
      by simpa [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] using e1 2 0,
      by simpa [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] using e1 2 1,
      by simpa [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] using e1 2 2⟩
    h2' (Y 0 0) (Y 0 1) (Y 0 2) (Y 1 0) (Y 1 1) (Y 1 2) (Y 2 0) (Y 2 1) (Y 2 2)
    ⟨by simpa [Matrix.mul_apply, Fin.sum_univ_three] using e3 0 0,
      by simpa [Matrix.mul_apply, Fin.sum_univ_three] using e3 0 1,
      by simpa [Matrix.mul_apply, Fin.sum_univ_three] using e3 0 2,
      by simpa [Matrix.mul_apply, Fin.sum_univ_three] using e3 1 0,
      by simpa [Matrix.mul_apply, Fin.sum_univ_three] using e3 1 1,
      by simpa [Matrix.mul_apply, Fin.sum_univ_three] using e3 1 2,
      by simpa [Matrix.mul_apply, Fin.sum_univ_three] using e3 2 0,
      by simpa [Matrix.mul_apply, Fin.sum_univ_three] using e3 2 1,
      by simpa [Matrix.mul_apply, Fin.sum_univ_three] using e3 2 2⟩
    (by simpa using d4)
  rcases key with ⟨c00, c01, c02, c10, c11, c12, c20, c21, c22⟩ |
    ⟨c00, c01, c02, c10, c11, c12, c20, c21, c22⟩
  · left
    apply Units.ext
    have : Y * Y = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] <;> assumption
    simpa [hY, pow_two] using this
  · right
    apply Units.ext
    have : Y * Y = S := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> assumption
    simpa [hY, hS, pow_two] using this

end CFSG.RankThree.PartTwo.Sec21.FF79
