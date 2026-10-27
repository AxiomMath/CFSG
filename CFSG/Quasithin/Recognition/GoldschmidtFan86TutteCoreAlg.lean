module

public import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.Fan86.Tutte

theorem rel7_alg {G : Type*} [Group G] (P X A B : G) (hP : P * P = 1) (hX : P * X * P = X⁻¹)
    (hA : P * A * P = X⁻¹ * B) (hAA : A * A = 1) (hBB : B * B = 1) :
    (P * X) * A * (P * (P * X) * P * X⁻¹) * B = 1 := by
  have h1 : (X⁻¹ * B) * (X⁻¹ * B) = 1 := by
    have : (P * A * P) * (P * A * P) = 1 := by
      calc (P * A * P) * (P * A * P) = P * (A * (P * P) * A) * P := by group
        _ = 1 := by rw [hP]; simp [hAA, hP]
    rwa [hA] at this
  have hBX : B * X⁻¹ * B = X := by
    have : X⁻¹ * B * X⁻¹ * B = 1 := by simpa [mul_assoc] using h1
    calc B * X⁻¹ * B = X * (X⁻¹ * B * X⁻¹ * B) := by group
      _ = X := by rw [this]; simp
  have hXP : X * P = P * X⁻¹ := by
    calc X * P = P * (P * X * P) := by calc X * P = (P * P) * X * P := by rw [hP]; simp
        _ = P * (P * X * P) := by group
      _ = P * X⁻¹ := by rw [hX]
  have hAP : A * P = P * (X⁻¹ * B) := by
    calc A * P = (P * P) * A * P := by rw [hP]; simp
      _ = P * (P * A * P) := by group
      _ = P * (X⁻¹ * B) := by rw [hA]
  have hmid : P * (P * X) * P = X * P := by
    calc P * (P * X) * P = (P * P) * X * P := by group
      _ = X * P := by rw [hP]; simp
  have hB2 : B * X⁻¹ * X⁻¹ * B = X * X := by
    calc B * X⁻¹ * X⁻¹ * B = (B * X⁻¹ * B) * (B * X⁻¹ * B) := by
          calc B * X⁻¹ * X⁻¹ * B = B * X⁻¹ * (B * B) * X⁻¹ * B := by rw [hBB]; simp
            _ = _ := by group
      _ = X * X := by rw [hBX]
  rw [hmid]
  calc P * X * A * (X * P * X⁻¹) * B = P * X * (A * P) * X⁻¹ * X⁻¹ * B := by
        calc P * X * A * (X * P * X⁻¹) * B = P * X * A * (X * P) * X⁻¹ * B := by group
          _ = P * X * A * (P * X⁻¹) * X⁻¹ * B := by rw [hXP]
          _ = P * X * (A * P) * X⁻¹ * X⁻¹ * B := by group
    _ = P * X * (P * (X⁻¹ * B)) * X⁻¹ * X⁻¹ * B := by rw [hAP]
    _ = P * (X * P) * (X⁻¹ * B) * X⁻¹ * X⁻¹ * B := by group
    _ = P * (P * X⁻¹) * (X⁻¹ * B) * X⁻¹ * X⁻¹ * B := by rw [hXP]
    _ = (P * P) * X⁻¹ * X⁻¹ * B * X⁻¹ * X⁻¹ * B := by group
    _ = X⁻¹ * X⁻¹ * (B * X⁻¹ * X⁻¹ * B) := by rw [hP]; group
    _ = 1 := by rw [hB2]; group

theorem rel8_alg {G : Type*} [Group G] (P X A B : G) (hPP : P * P = X)
    (hA : P * A * P⁻¹ = X * B⁻¹) (hB : P * B * P⁻¹ = X * A⁻¹) (hAA : A * A = 1)
    (hBB : B * B = 1) : (P * X) * A * (X * P) * B⁻¹ = 1 := by
  subst hPP
  have hAi : A⁻¹ = A := inv_eq_of_mul_eq_one_right hAA
  have h1 : (P * P * A⁻¹) * (P * P * A⁻¹) = 1 := by
    have e : (P * B * P⁻¹) * (P * B * P⁻¹) = 1 := by
      calc (P * B * P⁻¹) * (P * B * P⁻¹) = P * (B * B) * P⁻¹ := by group
        _ = 1 := by rw [hBB]; group
    rwa [hB] at e
  rw [hAi] at h1
  have h2 : B⁻¹ = P⁻¹ * A * P⁻¹ := by
    calc B⁻¹ = P⁻¹ * P⁻¹ * (P * P * B⁻¹) := by group
      _ = P⁻¹ * P⁻¹ * (P * A * P⁻¹) := by rw [hA]
      _ = P⁻¹ * A * P⁻¹ := by group
  rw [h2]
  calc P * (P * P) * A * (P * P * P) * (P⁻¹ * A * P⁻¹)
      = P * (P * P * A * (P * P * A)) * P⁻¹ := by group
    _ = 1 := by rw [h1]; group

theorem x_conj_alg {G : Type*} [Group G] (P X A B : G) (hP : P * P = 1)
    (hA : P * A * P = X⁻¹ * B) :
    X * A * X = (P * (P * X) * P * X⁻¹) * B * (P * X) := by
  have hB : B = X * (P * A * P) := by rw [hA]; group
  rw [hB]
  calc X * A * X = (P * P) * X * (P * P) * A * (P * P) * X := by rw [hP]; group
    _ = _ := by group

end CFSG.Quasithin.Fan86.Tutte
