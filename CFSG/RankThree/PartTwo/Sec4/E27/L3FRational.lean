module

public import CFSG.LieType.SeitzGeneration.OuterLinearDescent

public section

namespace CFSG.RankThree.PartTwo.Sec4.E27

open Matrix

section Rational

variable {F : Type} [Field F]

theorem inv_map_eq_of_map_eq {σ : F ≃+* F} {g' : GL (Fin 3) F}
    (hg : (g' : Matrix (Fin 3) (Fin 3) F).map σ = g') :
    ((g'⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map σ =
      ((g'⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
  set M : Matrix (Fin 3) (Fin 3) F := (g' : Matrix (Fin 3) (Fin 3) F)
  set N : Matrix (Fin 3) (Fin 3) F := ((g'⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
  have h1 : M * N = 1 := Units.mul_inv g'
  have h2 : N * M = 1 := Units.inv_mul g'
  have h3 : M * N.map σ = 1 := by
    have := congrArg (Matrix.map · σ) h1
    simpa [Matrix.map_mul, hg, Matrix.map_one σ (map_zero σ) (map_one σ)] using this
  calc N.map σ = (N * M) * N.map σ := by rw [h2, one_mul]
    _ = N * (M * N.map σ) := by rw [mul_assoc]
    _ = N := by rw [h3, mul_one]

variable [Finite F]

theorem exists_rational_rep_of_map {σ : F ≃+* F} (hσ : orderOf σ = 3) {k : Subfield F}
    (hk : ∀ x, x ∈ k ↔ σ x = x) {g₁ : GL (Fin 3) F} {c : Fˣ}
    (hmap : GeneralLinearGroup.map (σ : F →+* F) g₁ =
      g₁ * GeneralLinearGroup.scalar (Fin 3) c) :
    ∃ (u : Fˣ) (g' : GL (Fin 3) F), g₁ = GeneralLinearGroup.scalar (Fin 3) u * g' ∧
      ∀ i j, (g' : Matrix (Fin 3) (Fin 3) F) i j ∈ k := by
  set X : Matrix (Fin 3) (Fin 3) F := (g₁ : Matrix (Fin 3) (Fin 3) F) with hX
  have hX0 : X ≠ 0 := by
    intro h0
    have hdet : IsUnit X.det := Matrix.isUnits_det_units g₁
    rw [h0, Matrix.det_zero] at hdet
    exact not_isUnit_zero hdet
  have hXm : X.map σ = (c : F) • X := by
    have := congrArg (fun A : GL (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F)) hmap
    ext i j
    have h3 := congrFun (congrFun this i) j
    simpa [hX, GeneralLinearGroup.coe_scalar, Matrix.mul_apply, Matrix.scalar_apply,
      Matrix.diagonal_apply, mul_comm] using h3
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨ℓ, -, e, hℓ, hcard⟩ := FiniteField.card' F
  have hK : Nat.card F = ℓ ^ (e : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  obtain ⟨d, hd0, hd⟩ := CFSG.LieType.SeitzGeneration.exists_rational_smul Nat.prime_three hℓ
    e.pos hK σ hσ hX0 hXm
  refine ⟨(Units.mk0 d hd0)⁻¹, GeneralLinearGroup.scalar (Fin 3) (Units.mk0 d hd0) * g₁, ?_, ?_⟩
  · rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  · intro i j
    rw [hk]
    have h4 := congrFun (congrFun hd i) j
    simpa [hX, GeneralLinearGroup.coe_scalar, Matrix.mul_apply, Matrix.scalar_apply,
      Matrix.diagonal_apply] using h4

end Rational

end CFSG.RankThree.PartTwo.Sec4.E27
