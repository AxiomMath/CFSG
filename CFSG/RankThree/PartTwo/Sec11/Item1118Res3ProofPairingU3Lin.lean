module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofU3Lin

open scoped Matrix

theorem cube_root_cases {F : Type} [Field F] {μ ν : F} (hμ3 : μ ^ 3 = 1) (hμ1 : μ ≠ 1)
    (hν3 : ν ^ 3 = 1) : ν = 1 ∨ ν = μ ∨ ν = μ ^ 2 := by
  have hs : μ ^ 2 + μ + 1 = 0 := by
    have h : (μ - 1) * (μ ^ 2 + μ + 1) = 0 := by linear_combination hμ3
    exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hμ1)
  have h : (ν - 1) * ((ν - μ) * (ν - μ ^ 2)) = 0 := by
    linear_combination hν3 + (-ν ^ 2 + ν) * hs + (ν - 1) * hμ3
  rcases mul_eq_zero.1 h with h1 | h1
  · exact Or.inl (sub_eq_zero.1 h1)
  · rcases mul_eq_zero.1 h1 with h2 | h2
    · exact Or.inr (Or.inl (sub_eq_zero.1 h2))
    · exact Or.inr (Or.inr (sub_eq_zero.1 h2))

theorem exists_power_rot {Ω : Type} [Field Ω] {μ l : Ω} (hμ3 : μ ^ 3 = 1)
    (hl : l = μ ∨ l = μ ^ 2) (G : Matrix.GeneralLinearGroup (Fin 3) Ω)
    {X : Matrix (Fin 3) (Fin 3) Ω}
    (hGX : (G : Matrix (Fin 3) (Fin 3) Ω) * X =
      l • (X * (G : Matrix (Fin 3) (Fin 3) Ω))) :
    ∃ H : Matrix.GeneralLinearGroup (Fin 3) Ω, (H = G ∨ H = G⁻¹) ∧
      (H : Matrix (Fin 3) (Fin 3) Ω) * X = μ • (X * (H : Matrix (Fin 3) (Fin 3) Ω)) := by
  rcases hl with rfl | rfl
  · exact ⟨G, Or.inl rfl, hGX⟩
  · refine ⟨G⁻¹, Or.inr rfl, ?_⟩
    set A : Matrix (Fin 3) (Fin 3) Ω := (G : Matrix (Fin 3) (Fin 3) Ω) with hA
    set Ai : Matrix (Fin 3) (Fin 3) Ω := ((G⁻¹ : Matrix.GeneralLinearGroup (Fin 3) Ω) :
      Matrix (Fin 3) (Fin 3) Ω) with hAi
    have hAi1 : A * Ai = 1 := by
      rw [hA, hAi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hAi2 : Ai * A = 1 := by
      rw [hA, hAi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h3 : μ * μ ^ 2 = 1 := by rw [← hμ3]; ring
    have hXA : X * A = μ • (A * X) := by
      rw [hGX, smul_smul, h3, one_smul]
    have e1 : Ai * (X * A) * Ai = Ai * X := by
      simp only [Matrix.mul_assoc, hAi1, Matrix.mul_one]
    have e2 : Ai * (A * X) * Ai = X * Ai := by
      rw [← Matrix.mul_assoc, hAi2, Matrix.one_mul]
    calc Ai * X = Ai * (X * A) * Ai := e1.symm
      _ = Ai * (μ • (A * X)) * Ai := by rw [hXA]
      _ = μ • (Ai * (A * X) * Ai) := by rw [Matrix.mul_smul, Matrix.smul_mul]
      _ = μ • (X * Ai) := by rw [e2]

theorem mul_scalar_eq {Ω : Type} [Field Ω] (μ : Ω) (X : Matrix (Fin 3) (Fin 3) Ω) :
    X * Matrix.scalar (Fin 3) μ = μ • X := by
  ext i j
  simp [Matrix.scalar_apply, Matrix.mul_diagonal, mul_comm]

theorem scalar_pow_three_eq_one {Ω : Type} [Field Ω] {ν : Ω}
    (h : Matrix.scalar (Fin 3) ν ^ 3 = 1) : ν ^ 3 = 1 := by
  have h' : Matrix.scalar (Fin 3) (ν ^ 3) = Matrix.scalar (Fin 3) 1 := by
    rw [map_pow, map_one]
    exact h
  exact (Matrix.scalar (Fin 3)).injective h'

theorem eq_of_mat_eq {Ω : Type} [Field Ω] {R : Type} [Group R] {U : Subgroup (GL (Fin 3) Ω)}
    (e : R ≃* U) {x y : R}
    (h : (((e x : U) : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) =
      (((e y : U) : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω)) : x = y := by
  apply e.injective
  exact Subtype.ext (Units.ext h)

theorem central_mem_powers {Ω : Type} [Field Ω] {R : Type} [Group R] {U : Subgroup (GL (Fin 3) Ω)}
    (e : R ≃* U) {c d : R} {μ : Ω} (hμ3 : μ ^ 3 = 1) (hμ1 : μ ≠ 1)
    (hdμ : (((e d : U) : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) = Matrix.scalar (Fin 3) μ)
    (hcZ : ∃ ν : Ω, (((e c : U) : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) =
      Matrix.scalar (Fin 3) ν)
    (hc3 : c ^ 3 = 1) : c = 1 ∨ c = d ∨ c = d ^ 2 := by
  obtain ⟨ν, hν⟩ := hcZ
  have hpow : (((e c : U) : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) ^ 3 = 1 := by
    have h1 : (e c : U) ^ 3 = 1 := by rw [← map_pow, hc3, map_one]
    have h2 := congrArg (fun u : U => ((u : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω)) h1
    simpa [Subgroup.coe_pow, Units.val_pow_eq_pow_val] using h2
  have hν3 : ν ^ 3 = 1 := by
    apply scalar_pow_three_eq_one
    rw [← hν]
    exact hpow
  rcases cube_root_cases hμ3 hμ1 hν3 with h | h | h
  · refine Or.inl ?_
    apply eq_of_mat_eq e
    rw [hν, h]
    simp
  · refine Or.inr (Or.inl ?_)
    apply eq_of_mat_eq e
    rw [hν, h, hdμ]
  · refine Or.inr (Or.inr ?_)
    apply eq_of_mat_eq e
    have hd2 : (((e (d ^ 2) : U) : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) =
        Matrix.scalar (Fin 3) (μ ^ 2) := by
      rw [map_pow e d 2, Subgroup.coe_pow, Units.val_pow_eq_pow_val, hdμ,
        map_pow (Matrix.scalar (Fin 3)) μ 2]
    rw [hν, h, hd2]

theorem exists_conj_of_rot {Ω : Type} [Field Ω] {R : Type} [Group R] {U : Subgroup (GL (Fin 3) Ω)}
    (e : R ≃* U) {c d : R} {μ : Ω} (hμ3 : μ ^ 3 = 1) (hμ1 : μ ≠ 1)
    (hdμ : (((e d : U) : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) = Matrix.scalar (Fin 3) μ)
    (hdc : ∀ x : R, d * x = x * d)
    (hrot : ∃ G : GL (Fin 3) Ω, G ∈ U ∧ ∃ l : Ω, l ^ 3 = 1 ∧ l ≠ 1 ∧
      (G : Matrix (Fin 3) (Fin 3) Ω) * (((e c : U) : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) =
        l • ((((e c : U) : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) *
          (G : Matrix (Fin 3) (Fin 3) Ω))) :
    ∃ h : R, h * c * h⁻¹ = c * d ∧ h * d * h⁻¹ = d := by
  obtain ⟨G, hGU, l, hl3, hl1, hGX⟩ := hrot
  have hl : l = μ ∨ l = μ ^ 2 := by
    rcases cube_root_cases hμ3 hμ1 hl3 with h | h | h
    · exact absurd h hl1
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨H, hH, hHX⟩ := exists_power_rot hμ3 hl G hGX
  have hHU : H ∈ U := by
    rcases hH with rfl | rfl
    · exact hGU
    · exact U.inv_mem hGU
  have hm : e.symm ⟨H, hHU⟩ * c = c * d * e.symm ⟨H, hHU⟩ := by
    apply e.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [hdμ, mul_scalar_eq, Matrix.smul_mul]
    exact hHX
  refine ⟨e.symm ⟨H, hHU⟩, ?_, ?_⟩
  · rw [hm, mul_inv_cancel_right]
  · rw [← hdc (e.symm ⟨H, hHU⟩), mul_inv_cancel_right]

end CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofU3Lin

end
