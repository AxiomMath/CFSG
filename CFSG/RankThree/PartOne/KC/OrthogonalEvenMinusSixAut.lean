module

public import CFSG.LocalAnalysis.EvenBN.U4.Model.Aut
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusSixUnitary
public import CFSG.RankThree.PartOne.KC.UnitaryDefiningGramChange

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open CFSG.ClassicalGroups.UnitaryFlag
open scoped Matrix

section Swap

variable {E : Type} [Field E]

@[expose] def evenSixSwap (E : Type) [Field E] : Matrix (Fin 4) (Fin 4) E :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]

theorem evenSixSwap_mul_self : evenSixSwap E * evenSixSwap E = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [evenSixSwap, Matrix.mul_apply, Fin.sum_univ_four]

theorem evenSixSwap_gram {p f : ℕ} (h : UnitaryFieldData p f E) :
    ((evenSixSwap E).map h.bar)ᵀ * miyamotoJ4 E * evenSixSwap E = evenSixHerm E := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [evenSixSwap, miyamotoJ4, evenSixHerm, Matrix.mul_apply, Fin.sum_univ_four]

theorem evenSixSwap_map (τ : E ≃+* E) : (evenSixSwap E).map τ = evenSixSwap E := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [evenSixSwap]

theorem evenSix_map_congr (τ : E ≃+* E) (g : GL (Fin 4) E) (X : Matrix (Fin 4) (Fin 4) E) :
    ((g : Matrix (Fin 4) (Fin 4) E) * X * (g : Matrix (Fin 4) (Fin 4) E)ᵀ).map τ =
      (glAut τ g : Matrix (Fin 4) (Fin 4) E) * X.map τ *
        (glAut τ g : Matrix (Fin 4) (Fin 4) E)ᵀ := by
  rw [coe_glAut]
  ext i j
  simp [Matrix.mul_apply, Matrix.transpose_apply, map_sum, map_mul]

end Swap

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E]

theorem EvenNormPlane.exists_sixSU_aut_eq_conj_glAut (D : EvenNormPlane K E)
    (α : MulAut D.sixSU) :
    ∃ (s : D.sixSU) (τ : E ≃+* E), ∀ g : D.sixSU,
      ((α g : D.sixSU) : GL (Fin 4) E) =
        (s : GL (Fin 4) E) * glAut τ (g : GL (Fin 4) E) * (s : GL (Fin 4) E)⁻¹ := by
  obtain ⟨f, h, -, hbar⟩ := D.exists_unitaryFieldData
  have hS : D.sixSU = gramSU h (evenSixHerm E) := D.sixSU_eq_gramSU h hbar
  obtain ⟨P, hPv⟩ : ∃ P : GL (Fin 4) E, (P : Matrix (Fin 4) (Fin 4) E) = evenSixSwap E :=
    ⟨⟨evenSixSwap E, evenSixSwap E, evenSixSwap_mul_self, evenSixSwap_mul_self⟩, rfl⟩
  have hP : ((P : Matrix (Fin 4) (Fin 4) E).map h.bar)ᵀ * miyamotoJ4 E *
      (P : Matrix (Fin 4) (Fin 4) E) = evenSixHerm E := by
    rw [hPv]
    exact evenSixSwap_gram h
  obtain ⟨χ, hχ, hχs⟩ : ∃ χ : D.sixSU ≃* gramSU h (miyamotoJ4 E),
      (∀ x : D.sixSU,
        ((χ x : gramSU h (miyamotoJ4 E)) : GL (Fin 4) E) = P * (x : GL (Fin 4) E) * P⁻¹) ∧
      ∀ y : gramSU h (miyamotoJ4 E),
        ((χ.symm y : D.sixSU) : GL (Fin 4) E) = P⁻¹ * (y : GL (Fin 4) E) * P⁻¹⁻¹ :=
    ⟨(MulEquiv.subgroupCongr hS).trans
      (CFSG.RankThree.PartOne.KCUnitaryDefining.gramChangeSU h P hP), fun _ => rfl, fun _ => rfl⟩
  obtain ⟨s', hs'⟩ :=
    CFSG.LocalAnalysis.EvenBN.U4.exists_eq_conj_mul_fieldAut h (MulAut.congr χ α)
  generalize CFSG.LocalAnalysis.EvenBN.U4.miyamotoFieldFactor h (MulAut.congr χ α) = τ at hs'
  have hPτ : glAut τ P = P := Units.ext (by rw [coe_glAut, hPv]; exact evenSixSwap_map τ)
  refine ⟨χ.symm s', τ, fun g => ?_⟩
  have h1 := congrArg (fun β : MulAut (gramSU h (miyamotoJ4 E)) =>
    ((β (χ g) : gramSU h (miyamotoJ4 E)) : GL (Fin 4) E)) hs'
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
    CFSG.LocalAnalysis.EvenBN.U4.coe_miyamotoFieldAut_apply] at h1
  rw [hχ, hχ, map_mul, map_mul, map_inv, hPτ] at h1
  have h2 : ((α g : D.sixSU) : GL (Fin 4) E) =
      P⁻¹ * (P * ((α g : D.sixSU) : GL (Fin 4) E) * P⁻¹) * P := by
    simp only [mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left]
  rw [h2, h1, hχs]
  simp only [mul_inv_rev, inv_inv, mul_assoc]

theorem EvenNormPlane.sigma_comm_ringEquiv (D : EvenNormPlane K E) (τ : E ≃+* E) (z : E) :
    D.σ (τ z) = τ (D.σ z) := by
  rw [D.sigma_eq_pow, D.sigma_eq_pow, map_pow]

theorem EvenNormPlane.map_mem_sixSpace (D : EvenNormPlane K E) (τ : E ≃+* E)
    {X : Matrix (Fin 4) (Fin 4) E} (hX : X ∈ D.sixSpace) : X.map τ ∈ D.sixSpace := by
  obtain ⟨⟨hT, hd⟩, hs⟩ := hX
  refine ⟨⟨by rw [← Matrix.transpose_map, hT], fun i => by simp [hd i]⟩, ?_⟩
  have h1 : sharp (X.map τ) = (sharp X).map τ := by
    simp only [sharp, Matrix.map_apply]
    rw [evenSix_map_altMat]
  have h2 : (X.map τ).map D.σ = (X.map D.σ).map τ := by
    ext i j
    simp [D.sigma_comm_ringEquiv]
  have key : ∀ M N : Matrix (Fin 4) (Fin 4) E, (M * N).map τ = M.map τ * N.map τ :=
    fun M N => Matrix.map_mul (f := (τ : E →+* E))
  rw [h1, h2, hs, key, key, evenSixHerm_map]

@[expose] def EvenNormPlane.sixSpaceField (D : EvenNormPlane K E) (τ : E ≃+* E) :
    D.sixSpace ≃+ D.sixSpace where
  toFun X := ⟨(X : Matrix (Fin 4) (Fin 4) E).map τ, D.map_mem_sixSpace τ X.2⟩
  invFun X := ⟨(X : Matrix (Fin 4) (Fin 4) E).map τ.symm, D.map_mem_sixSpace τ.symm X.2⟩
  left_inv X := Subtype.ext (by ext i j; simp)
  right_inv X := Subtype.ext (by ext i j; simp)
  map_add' X Y := Subtype.ext (by ext i j; simp)

theorem EvenNormPlane.coe_sixSpaceField (D : EvenNormPlane K E) (τ : E ≃+* E) (X : D.sixSpace) :
    ((D.sixSpaceField τ X : D.sixSpace) : Matrix (Fin 4) (Fin 4) E) =
      (X : Matrix (Fin 4) (Fin 4) E).map τ := rfl

theorem EvenNormPlane.sixSpace_intertwine_of_aut_eq_conj_field
    (D : EvenNormPlane K E) (α : MulAut D.sixSU) (s : D.sixSU) (τ : E ≃+* E)
    (hsτ : ∀ g : D.sixSU, ((α g : D.sixSU) : GL (Fin 4) E) =
      (s : GL (Fin 4) E) * glAut τ (g : GL (Fin 4) E) * (s : GL (Fin 4) E)⁻¹) :
    ∀ (g : D.sixSU) (X : D.sixSpace),
      ((D.sixSpaceField τ).trans (D.sixRho s).toAddEquiv) (D.sixRho g X) =
        D.sixRho (α g) (((D.sixSpaceField τ).trans (D.sixRho s).toAddEquiv) X) := by
  intro g X
  apply Subtype.ext
  change ((s : GL (Fin 4) E) : Matrix (Fin 4) (Fin 4) E) *
      (((g : GL (Fin 4) E) : Matrix (Fin 4) (Fin 4) E) * (X : Matrix (Fin 4) (Fin 4) E) *
        ((g : GL (Fin 4) E) : Matrix (Fin 4) (Fin 4) E)ᵀ).map τ *
      ((s : GL (Fin 4) E) : Matrix (Fin 4) (Fin 4) E)ᵀ =
    (((α g : D.sixSU) : GL (Fin 4) E) : Matrix (Fin 4) (Fin 4) E) *
      (((s : GL (Fin 4) E) : Matrix (Fin 4) (Fin 4) E) * (X : Matrix (Fin 4) (Fin 4) E).map τ *
        ((s : GL (Fin 4) E) : Matrix (Fin 4) (Fin 4) E)ᵀ) *
      (((α g : D.sixSU) : GL (Fin 4) E) : Matrix (Fin 4) (Fin 4) E)ᵀ
  rw [hsτ g, evenSix_map_congr]
  have hss : (((s : GL (Fin 4) E)⁻¹ : GL (Fin 4) E) : Matrix (Fin 4) (Fin 4) E) *
      ((s : GL (Fin 4) E) : Matrix (Fin 4) (Fin 4) E) = 1 := Units.inv_mul _
  have hssT : ((s : GL (Fin 4) E) : Matrix (Fin 4) (Fin 4) E)ᵀ *
      (((s : GL (Fin 4) E)⁻¹ : GL (Fin 4) E) : Matrix (Fin 4) (Fin 4) E)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, hss, Matrix.transpose_one]
  simp only [Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (((s : GL (Fin 4) E)⁻¹ : GL (Fin 4) E) : Matrix (Fin 4) (Fin 4) E),
    hss, Matrix.one_mul, ← Matrix.mul_assoc ((s : GL (Fin 4) E) : Matrix (Fin 4) (Fin 4) E)ᵀ,
    hssT, Matrix.one_mul]

theorem EvenNormPlane.exists_sixSpace_intertwine (D : EvenNormPlane K E) (α : MulAut D.sixSU) :
    ∃ B : D.sixSpace ≃+ D.sixSpace, ∀ (g : D.sixSU) (X : D.sixSpace),
      B (D.sixRho g X) = D.sixRho (α g) (B X) := by
  obtain ⟨s, τ, hsτ⟩ := D.exists_sixSU_aut_eq_conj_glAut α
  exact ⟨(D.sixSpaceField τ).trans (D.sixRho s).toAddEquiv,
    D.sixSpace_intertwine_of_aut_eq_conj_field α s τ hsτ⟩

end CFSG.RankThree.PartOne.KCOrthogonal
