module

public import CFSG.Quasithin.Vol2.Ch10SecALiftConj

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

variable {F : Type} [Field F]

theorem lower_left_eq_zero {h : Matrix.SpecialLinearGroup (Fin 2) F} {b : F}
    (hb : h * unipSL 1 * h⁻¹ = unipSL b) : (h : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  have h1 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
    (A : Matrix (Fin 2) (Fin 2) F) 1 0) hb
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    coe_unipSL, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two] at h1
  simp at h1
  have h2 : -((h : Matrix (Fin 2) (Fin 2) F) 1 0 ^ 2) = 0 := by linear_combination h1
  simpa using h2

theorem eq_one_of_natural [CharP F 2] {g h : Matrix.SpecialLinearGroup (Fin 2) F}
    (hodd : Odd (orderOf h))
    (hN : ∀ b : F, ∃ b' : F, h * (g⁻¹ * unipSL b * g) * h⁻¹ = g⁻¹ * unipSL b' * g)
    {v : Fin 2 → F} (hv : v ≠ 0)
    (hu : (unipSL 1 : Matrix.SpecialLinearGroup (Fin 2) F).1.mulVec
      ((g : Matrix (Fin 2) (Fin 2) F).mulVec v) = (g : Matrix (Fin 2) (Fin 2) F).mulVec v)
    (hfix : (h : Matrix (Fin 2) (Fin 2) F).mulVec v = v) : h = 1 := by
  set h' := g * h * g⁻¹ with hh'
  obtain ⟨b', hb'⟩ := hN 1
  have hb'' : h' * unipSL 1 * h'⁻¹ = unipSL b' := by
    rw [hh']
    calc g * h * g⁻¹ * unipSL 1 * (g * h * g⁻¹)⁻¹
        = g * (h * (g⁻¹ * unipSL 1 * g) * h⁻¹) * g⁻¹ := by group
      _ = g * (g⁻¹ * unipSL b' * g) * g⁻¹ := by rw [hb']
      _ = unipSL b' := by group
  have hr := lower_left_eq_zero hb''
  set w := (g : Matrix (Fin 2) (Fin 2) F).mulVec v with hw
  have hw1 : w 1 = 0 := by
    have h1 := congrFun hu 0
    rw [coe_unipSL, unipSL_mulVec] at h1
    simpa using h1
  have hw0 : w 0 ≠ 0 := by
    intro h0
    apply hv
    have hw' : w = 0 := by
      ext i
      fin_cases i
      · exact h0
      · exact hw1
    have := congrArg (fun u => ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F).mulVec u) hw'
    simp only [hw, Matrix.mulVec_mulVec, coe_inv_mul_SL, Matrix.one_mulVec,
      Matrix.mulVec_zero] at this
    exact this
  have hfix' : (h' : Matrix (Fin 2) (Fin 2) F).mulVec w = w := by
    rw [hh', hw, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, coe_inv_mul_SL, Matrix.mul_one,
      ← Matrix.mulVec_mulVec, hfix]
  have ha : (h' : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    have h1 := congrFun hfix' 0
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hw1] at h1
    have : ((h' : Matrix (Fin 2) (Fin 2) F) 0 0 - 1) * w 0 = 0 := by linear_combination h1
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hw0)
  have hdet := Matrix.SpecialLinearGroup.det_coe h'
  rw [Matrix.det_fin_two, ha, hr, one_mul, mul_zero, sub_zero] at hdet
  have hsq : h' * h' = 1 := by
    have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ha, hr, hdet]
    linear_combination ((h' : Matrix (Fin 2) (Fin 2) F) 0 1) * h2
  have hord : orderOf h' = orderOf h := by
    rw [hh', show g * h * g⁻¹ = (MulAut.conj g).toMonoidHom h from rfl,
      orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective]
  have hdvd : orderOf h' ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq, hsq])
  rw [hord] at hdvd
  have h1 : orderOf h = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact h
    · exfalso
      rw [h] at hodd
      exact (Nat.not_even_iff_odd.mpr hodd) even_two
  exact orderOf_eq_one_iff.mp h1

end CFSG.Quasithin.Vol2.Ch10.SecA
