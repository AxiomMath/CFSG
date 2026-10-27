module

public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusSixDefs

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Module Matrix CFSG.LocalAnalysis

section Congruence

variable {K : Type} [Field K] [Finite K] [CharP K 2] {E : Type} [Field E] [Algebra K E]
  (D : EvenNormPlane K E)

theorem EvenNormPlane.congr_mem_sixSpace {g : GL (Fin 4) E} (hg : g ∈ D.sixSU)
    {X : Matrix (Fin 4) (Fin 4) E} (hX : X ∈ D.sixSpace) :
    (g : Matrix (Fin 4) (Fin 4) E) * X * (g : Matrix (Fin 4) (Fin 4) E)ᵀ ∈ D.sixSpace := by
  have : CharP E 2 := charP_two_of_algebra (K := K)
  obtain ⟨hgH, hdet⟩ := hg
  obtain ⟨hX1, hX2⟩ := hX
  obtain ⟨-, -, -, -, h5⟩ := char_two_alternating_four_Pfaffian_identities (F := E)
  obtain ⟨halt, -, hsharp⟩ := h5 g X hX1
  refine ⟨halt, ?_⟩
  rw [hsharp, hdet, one_smul, hX2]
  set G := (g : Matrix (Fin 4) (Fin 4) E)
  set Gi := ((g⁻¹ : GL (Fin 4) E) : Matrix (Fin 4) (Fin 4) E)
  have hGGi : G * Gi = 1 := Units.mul_inv g
  have hR1 : (G.map D.σ)ᵀ * evenSixHerm E = evenSixHerm E * Gi := by
    calc (G.map D.σ)ᵀ * evenSixHerm E
        = (G.map D.σ)ᵀ * evenSixHerm E * (G * Gi) := by rw [hGGi, Matrix.mul_one]
      _ = ((G.map D.σ)ᵀ * evenSixHerm E * G) * Gi := by simp only [Matrix.mul_assoc]
      _ = evenSixHerm E * Gi := by rw [hgH]
  have hR2 : Giᵀ * evenSixHerm E = evenSixHerm E * G.map D.σ := by
    have := congrArg Matrix.transpose hR1
    rw [transpose_mul, transpose_mul, transpose_transpose, evenSixHerm_transpose] at this
    exact this.symm
  have hmap : (G * X * Gᵀ).map D.σ = G.map D.σ * X.map D.σ * (G.map D.σ)ᵀ := by
    rw [Matrix.map_mul, Matrix.map_mul, transpose_map]
  rw [hmap]
  calc Giᵀ * (evenSixHerm E * X.map D.σ * evenSixHerm E) * Gi
      = (Giᵀ * evenSixHerm E) * X.map D.σ * (evenSixHerm E * Gi) := by
        simp only [Matrix.mul_assoc]
    _ = (evenSixHerm E * G.map D.σ) * X.map D.σ * ((G.map D.σ)ᵀ * evenSixHerm E) := by
        rw [hR2, hR1]
    _ = evenSixHerm E * (G.map D.σ * X.map D.σ * (G.map D.σ)ᵀ) * evenSixHerm E := by
        simp only [Matrix.mul_assoc]

@[expose] def EvenNormPlane.sixCongr (g : D.sixSU) : D.sixSpace →ₗ[K] D.sixSpace where
  toFun X := ⟨((g : GL (Fin 4) E) : Matrix (Fin 4) (Fin 4) E) * X.1 *
    ((g : GL (Fin 4) E) : Matrix (Fin 4) (Fin 4) E)ᵀ, D.congr_mem_sixSpace g.2 X.2⟩
  map_add' X Y := Subtype.ext (by simp [Matrix.mul_add, Matrix.add_mul])
  map_smul' c X := Subtype.ext (by simp)

theorem EvenNormPlane.coe_sixCongr (g : D.sixSU) (X : D.sixSpace) :
    (D.sixCongr g X : Matrix (Fin 4) (Fin 4) E) =
      ((g : GL (Fin 4) E) : Matrix (Fin 4) (Fin 4) E) * X *
        ((g : GL (Fin 4) E) : Matrix (Fin 4) (Fin 4) E)ᵀ :=
  rfl

theorem EvenNormPlane.sixCongr_mul (g h : D.sixSU) (X : D.sixSpace) :
    D.sixCongr (g * h) X = D.sixCongr g (D.sixCongr h X) := by
  refine Subtype.ext ?_
  simp only [EvenNormPlane.coe_sixCongr, Subgroup.coe_mul, Units.val_mul, transpose_mul]
  simp only [Matrix.mul_assoc]

theorem EvenNormPlane.sixCongr_one (X : D.sixSpace) : D.sixCongr 1 X = X := by
  refine Subtype.ext ?_
  simp [EvenNormPlane.coe_sixCongr]

theorem EvenNormPlane.sixForm_sixCongr (g : D.sixSU) (X : D.sixSpace) :
    D.sixForm (D.sixCongr g X) = D.sixForm X := by
  have : CharP E 2 := charP_two_of_algebra (K := K)
  apply (algebraMap K E).injective
  rw [D.algebraMap_sixForm, D.algebraMap_sixForm]
  obtain ⟨-, -, -, -, h5⟩ := char_two_alternating_four_Pfaffian_identities (F := E)
  obtain ⟨-, hp, -⟩ := h5 (g : GL (Fin 4) E) X.1 X.2.1
  rw [EvenNormPlane.coe_sixCongr, hp, g.2.2, one_mul]

@[expose] noncomputable def EvenNormPlane.sixRho :
    D.sixSU →* (D.sixSpace ≃ₗ[K] D.sixSpace) :=
  MonoidHom.mk' (fun g => LinearEquiv.ofLinearMap (D.sixCongr g) (D.sixCongr g⁻¹)
    (LinearMap.ext fun X => by
      rw [LinearMap.comp_apply, ← D.sixCongr_mul, mul_inv_cancel, D.sixCongr_one]; rfl)
    (LinearMap.ext fun X => by
      rw [LinearMap.comp_apply, ← D.sixCongr_mul, inv_mul_cancel, D.sixCongr_one]; rfl))
    (fun g h => LinearEquiv.ext fun X => by
      simp only [LinearEquiv.coe_ofLinearMap, LinearEquiv.mul_apply]
      exact D.sixCongr_mul g h X)

theorem EvenNormPlane.coe_sixRho (g : D.sixSU) (X : D.sixSpace) :
    ((D.sixRho g X : D.sixSpace) : Matrix (Fin 4) (Fin 4) E) =
      ((g : GL (Fin 4) E) : Matrix (Fin 4) (Fin 4) E) * X *
        ((g : GL (Fin 4) E) : Matrix (Fin 4) (Fin 4) E)ᵀ :=
  rfl

theorem EvenNormPlane.sixRho_mem (g : D.sixSU) :
    D.sixRho g ∈ TauCeti.QuadraticMap.orthogonalGroup D.sixForm := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro X
  exact D.sixForm_sixCongr g X

theorem EvenNormPlane.sixRho_range_le :
    D.sixRho.range ≤ TauCeti.QuadraticMap.orthogonalGroup D.sixForm := by
  rintro _ ⟨g, rfl⟩
  exact D.sixRho_mem g

end Congruence

end CFSG.RankThree.PartOne.KCOrthogonal
