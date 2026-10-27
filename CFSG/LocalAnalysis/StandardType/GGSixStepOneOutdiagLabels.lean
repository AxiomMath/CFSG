module

public import CFSG.LocalAnalysis.StandardType.GGSixStepOneOutdiagInputs

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Inn

theorem ggInndiagNormal_innSet (R : Type) [Group R] : GGInndiagNormal R (LargeEvenInnSet R) :=
  ggInndiagNormal_of_subset_inn fun _ ⟨r, hr⟩ => ⟨r, hr⟩

variable {K : Type} [Field K]

theorem matConjImage_gsp_subset_inn [Finite K] [CharP K 2] (m : ℕ) :
    LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m) ⊆
      (MulAut.conj : LargeEvenProj (LargeEvenSpGroup K m) →*
        MulAut (LargeEvenProj (LargeEvenSpGroup K m))).range := by
  rintro φ ⟨A, ⟨μ, hμ0, hA⟩, hφ⟩
  have := Fintype.ofFinite K
  obtain ⟨l, hl⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) μ
  have hl0 : l ≠ 0 := by
    rintro rfl
    exact hμ0 (by rw [hl, zero_mul])
  set A' := Matrix.GeneralLinearGroup.scalar _ (Units.mk0 l⁻¹ (inv_ne_zero hl0)) * A with hA'
  have hA'Sp : A' ∈ LargeEvenSpGroup K m :=
    Subgroup.subset_closure (TableB.exists_scalar_mul_mem_sp hA hl0 hl)
  have hconj : ∀ h : GL (Fin m ⊕ Fin m) K, A' * h * A'⁻¹ = A * h * A⁻¹ := by
    intro h
    have hc := Subgroup.mem_center_iff.mp
      (TableB.scalar_mem_center (ι := Fin m ⊕ Fin m) (Units.mk0 l⁻¹ (inv_ne_zero hl0)))
    rw [hA', mul_inv_rev]
    set s := Matrix.GeneralLinearGroup.scalar (Fin m ⊕ Fin m) (Units.mk0 l⁻¹ (inv_ne_zero hl0))
    calc s * A * h * (A⁻¹ * s⁻¹) = s * (A * h * A⁻¹) * s⁻¹ := by group
      _ = (A * h * A⁻¹) * s * s⁻¹ := by rw [hc (A * h * A⁻¹)]
      _ = A * h * A⁻¹ := by group
  obtain ⟨a, ha⟩ : ∃ a : LargeEvenSpGroup K m, (a : GL (Fin m ⊕ Fin m) K) = A' :=
    ⟨⟨A', hA'Sp⟩, rfl⟩
  refine ⟨(a : LargeEvenProj (LargeEvenSpGroup K m)), ?_⟩
  ext x
  induction x using QuotientGroup.induction_on with
  | H h =>
    rw [MulAut.conj_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    have hrel : ((a * h * a⁻¹ : LargeEvenSpGroup K m) : GL (Fin m ⊕ Fin m) K) = A * h * A⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ha]
      exact hconj h
    exact (hφ h (a * h * a⁻¹) hrel).symm

end Inn

section Labels

theorem recipeOmegaPlus_inndiag {m q : ℕ} {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeOmegaPlus m q Q) :
    LargeEvenRecipeOmegaPlus m q fun R _ I F =>
      Q R I F ∧ LargeEvenSimpleGuard (fun R _ I _ => GGInndiagNormal R I) R I F := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hQ, fun _ _ => ggInndiagNormal_innSet _⟩

theorem recipeOmegaMinus_inndiag {m q : ℕ} {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeOmegaMinus m q Q) :
    LargeEvenRecipeOmegaMinus m q fun R _ I F =>
      Q R I F ∧ LargeEvenSimpleGuard (fun R _ I _ => GGInndiagNormal R I) R I F := by
  obtain ⟨K, _, _, hK, b, c, hbc, hQ⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hQ,
    fun _ _ => ggInndiagNormal_innSet _⟩

theorem recipeSuzuki_inndiag {a : ℕ} {Q : LargeEvenRawCont} (h : LargeEvenRecipeSuzuki a Q) :
    LargeEvenRecipeSuzuki a fun R _ I F =>
      Q R I F ∧ LargeEvenSimpleGuard (fun R _ I _ => GGInndiagNormal R I) R I F := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hQ, fun _ _ => ggInndiagNormal_innSet _⟩

theorem recipeSymplectic_inndiag {m n : ℕ} {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeSymplectic m (2 ^ n) false Q) :
    LargeEvenRecipeSymplectic m (2 ^ n) false fun R _ I F =>
      Q R I F ∧ LargeEvenSimpleGuard (fun R _ I _ => GGInndiagNormal R I) R I F := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have := charP_two_of_card hK
  exact ⟨K, inferInstance, inferInstance, hK, hQ,
    fun _ _ => ggInndiagNormal_of_subset_inn (matConjImage_gsp_subset_inn m)⟩

@[expose] def GGInndiagInnLabel (lab : LargeEvenLabel) : Prop :=
  lab.tag = .B ∨ lab.tag = .C ∨ (lab.tag = .D ∧ lab.rank ≠ 3) ∨
    (lab.tag = .twD ∧ lab.rank ≠ 2 ∧ lab.rank ≠ 3) ∨ lab.tag = .twB2

theorem largeEvenLabelAll_inndiag_inn {lab : LargeEvenLabel} (h : GGInndiagInnLabel lab) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => GGInndiagNormal R I) := by
  obtain ⟨t, l, n⟩ := lab
  intro Q hQ
  rcases h with h | h | ⟨h, hl⟩ | ⟨h, hl2, hl3⟩ | h
  · dsimp only at h
    subst h
    exact recipeSymplectic_inndiag hQ
  · dsimp only at h
    subst h
    exact recipeSymplectic_inndiag hQ
  · dsimp only at h hl
    subst h
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    simp only [hl, ↓reduceIte] at hQ ⊢
    exact recipeOmegaPlus_inndiag hQ
  · dsimp only at h hl2 hl3
    subst h
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    simp only [hl2, hl3, ↓reduceIte] at hQ ⊢
    exact recipeOmegaMinus_inndiag hQ
  · dsimp only at h
    subst h
    exact recipeSuzuki_inndiag hQ

@[expose] def GGInndiagNormalRestInput : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → ¬ GGInndiagInnLabel lab →
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => GGInndiagNormal R I)

theorem ggInndiagNormalInput_of_rest (h : GGInndiagNormalRestInput) : GGInndiagNormalInput := by
  intro lab hlab
  by_cases hi : GGInndiagInnLabel lab
  · exact largeEvenLabelAll_inndiag_inn hi
  · exact h lab hlab hi

end Labels

end CFSG.StandardType
