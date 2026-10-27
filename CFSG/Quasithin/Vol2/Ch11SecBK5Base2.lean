module

public import CFSG.Quasithin.Vol2.Ch11SecBK8Base10

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K5

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Assembly.LowTwoRank K8

variable {K : Type} [Field K]


theorem tens_eq_one {A : GL (Fin 3) K} {M : GL (Fin 2) K} (h : tensHom (A, M) = 1) :
    ∃ ν : K, ν ≠ 0 ∧ (M : Matrix (Fin 2) (Fin 2) K) = ν • 1 ∧
      (A : Matrix (Fin 3) (Fin 3) K) = ν⁻¹ • 1 := by
  have h1 : tensMat (A : Matrix (Fin 3) (Fin 3) K) (M : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [← coe_tensHom, h, Units.val_one]
  obtain ⟨h01, h10, h00⟩ := eq_of_tensMat_eq_one h1
  set ν := (M : Matrix (Fin 2) (Fin 2) K) 0 0 with hν
  have hM : (M : Matrix (Fin 2) (Fin 2) K) = ν • 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h10, ← h00, hν]
  have hA : ν • (A : Matrix (Fin 3) (Fin 3) K) = 1 := by
    ext i j
    have := congrFun (congrFun h1 (Sum.inl i)) (Sum.inl j)
    simpa [tensMat, Matrix.fromBlocks, Matrix.one_apply] using this
  have hν0 : ν ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hA
    have := congrFun (congrFun hA 0) 0
    simp at this
  refine ⟨ν, hν0, hM, ?_⟩
  rw [← hA, smul_smul, inv_mul_cancel₀ hν0, one_smul]

theorem fst_comm {A A' : GL (Fin 3) K} {M M' : GL (Fin 2) K}
    (h : tensHom (A, M) * tensHom (A', M') = tensHom (A', M') * tensHom (A, M)) :
    A * A' = A' * A := by
  have h1 : tensHom ((A * A') * (A' * A)⁻¹, (M * M') * (M' * M)⁻¹) = 1 := by
    have e : ((A * A') * (A' * A)⁻¹, (M * M') * (M' * M)⁻¹) =
        ((A, M) * (A', M')) * ((A', M') * (A, M))⁻¹ := rfl
    rw [e, map_mul, map_inv, map_mul, map_mul, h, mul_inv_cancel]
  obtain ⟨ν, hν0, hM, hA⟩ := tens_eq_one h1
  have hdetA := congrArg Matrix.det hA
  have hdetM := congrArg Matrix.det hM
  rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdetA hdetM
  have hd : ∀ (n : ℕ) (X Y : GL (Fin n) K),
      (((X * Y) * (Y * X)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 := by
    intro n X Y
    have h2 : Matrix.GeneralLinearGroup.det ((X * Y) * (Y * X)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, mul_comm (Matrix.GeneralLinearGroup.det Y),
        mul_inv_cancel]
    have h3 := congrArg (fun g : Kˣ => (g : K)) h2
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using h3
  rw [hd] at hdetA hdetM
  have hν3 : ν ^ 3 = 1 := by
    have := congrArg (fun x => x⁻¹) hdetA
    simpa using this.symm
  have hν1 : ν = 1 := by
    have h2 : ν ^ 2 = 1 := hdetM.symm
    calc ν = ν ^ 3 / ν ^ 2 := by field_simp
      _ = 1 := by rw [hν3, h2, div_one]
  rw [hν1, inv_one, one_smul] at hA
  have h3 : (A * A') * (A' * A)⁻¹ = 1 := Units.ext (by rw [hA, Units.val_one])
  exact mul_inv_eq_one.mp h3

end CFSG.Quasithin.Vol2.Ch11.SecB.K5
