module

public import CFSG.LocalAnalysis.StandardType.GGSixStepOneOutdiagLabels
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration

public section

namespace CFSG.StandardType

open Matrix CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Linear

variable {d : ℕ} {K : Type} [Field K]

theorem congr_symm_conjAut_mem (A : GL (Fin d) K) :
    (MulAut.congr (TypeA.recipeEquiv d K)).symm (conjAut d K A) ∈
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ := by
  refine ⟨A, Set.mem_univ _, fun h h' hrel => ?_⟩
  rw [MulAut.congr_symm_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_eq, TypeA.recipeEquiv_mk, TypeA.recipeEquiv_mk, conjAut_proj]
  apply congrArg (proj d K)
  ext i j
  rw [TypeA.coe_slConjugation', TypeA.coe_slKerEquiv, TypeA.coe_slKerEquiv, hrel]
  rfl

theorem ggInndiagNormal_linear [Finite K] (hd : 3 ≤ d) :
    GGInndiagNormal (LargeEvenProj (LargeEvenSLGroup (Fin d) K))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ) := by
  intro α φ hφ
  set c := MulAut.congr (TypeA.recipeEquiv d K) with hc
  obtain ⟨-, -, hDnorm, -⟩ := standard_outer_quotients (n := d) (K := K)
  have htop := (automorphism_generation (K := K) hd).1
  have hDN : ∀ β : MulAut (projectiveSL d K), ∀ y ∈ linearAutGroup d K,
      β * y * β⁻¹ ∈ linearAutGroup d K := by
    intro β y hy
    have hβ : β ∈ standardAutGroup d K := htop ▸ Subgroup.mem_top β
    have hy' : y ∈ standardAutGroup d K := htop ▸ Subgroup.mem_top y
    have := (Subgroup.normal_subgroupOf_iff (H := linearAutGroup d K)
      (K := standardAutGroup d K) (fun z _ => htop ▸ Subgroup.mem_top z)).mp hDnorm y β hy hβ
    exact this
  have hDle : linearAutGroup d K ≤
      (ggInndiag (LargeEvenProj (LargeEvenSLGroup (Fin d) K))
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ)).map
          c.toMonoidHom := by
    rw [linearAutGroup, Subgroup.closure_le]
    rintro _ ⟨A, rfl⟩
    exact ⟨c.symm (conjAut d K A), subset_ggInndiag (congr_symm_conjAut_mem A),
      c.apply_symm_apply _⟩
  have hmem : c (α * φ * α⁻¹) ∈ linearAutGroup d K := by
    rw [map_mul, map_mul, map_inv]
    obtain ⟨A, hA⟩ := TypeA.congr_recipeEquiv_mem hφ
    refine hDN (c α) _ ?_
    rw [← hA]
    exact Subgroup.subset_closure ⟨A, rfl⟩
  obtain ⟨y, hy, hyc⟩ := hDle hmem
  have : y = α * φ * α⁻¹ := c.injective hyc
  rwa [← this]

end Linear

section Two

variable {K : Type} [Field K]

theorem matConjImage_two_subset_inn [Finite K] [CharP K 2] :
    LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) K)) Set.univ ⊆
      (MulAut.conj : LargeEvenProj (LargeEvenSLGroup (Fin 2) K) →*
        MulAut (LargeEvenProj (LargeEvenSLGroup (Fin 2) K))).range := by
  rintro φ ⟨A, -, hφ⟩
  have := Fintype.ofFinite K
  have hdet0 : (A : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  obtain ⟨l, hl⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2)
    (A : Matrix (Fin 2) (Fin 2) K).det
  have hl0 : l ≠ 0 := by
    rintro rfl
    exact hdet0 (by rw [hl, zero_mul])
  set s := Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 l⁻¹ (inv_ne_zero hl0)) with hs
  set A' := s * A with hA'
  have hdet : ((A' : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    rw [hA', Units.val_mul, det_mul, hs, Matrix.GeneralLinearGroup.coe_scalar, scalar_apply,
      det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hl]
    change l⁻¹ ^ 2 * (l * l) = 1
    field_simp
  have hA'SL : A' ∈ LargeEvenSLGroup (Fin 2) K := TypeA.mem_largeEvenSLGroup_iff.mpr hdet
  have hconj : ∀ h : GL (Fin 2) K, A' * h * A'⁻¹ = A * h * A⁻¹ := by
    intro h
    have hc := Subgroup.mem_center_iff.mp
      (TableB.scalar_mem_center (ι := Fin 2) (Units.mk0 l⁻¹ (inv_ne_zero hl0)))
    rw [hA', _root_.mul_inv_rev]
    calc s * A * h * (A⁻¹ * s⁻¹) = s * (A * h * A⁻¹) * s⁻¹ := by group
      _ = (A * h * A⁻¹) * s * s⁻¹ := by rw [hc (A * h * A⁻¹)]
      _ = A * h * A⁻¹ := by group
  obtain ⟨a, ha⟩ : ∃ a : LargeEvenSLGroup (Fin 2) K, (a : GL (Fin 2) K) = A' :=
    ⟨⟨A', hA'SL⟩, rfl⟩
  refine ⟨(a : LargeEvenProj (LargeEvenSLGroup (Fin 2) K)), ?_⟩
  ext x
  induction x using QuotientGroup.induction_on with
  | H h =>
    rw [MulAut.conj_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    have hrel : ((a * h * a⁻¹ : LargeEvenSLGroup (Fin 2) K) : GL (Fin 2) K) = A * h * A⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ha]
      exact hconj h
    exact (hφ h (a * h * a⁻¹) hrel).symm

end Two

section Labels

theorem recipeLinear_inndiag {d m : ℕ} (hd : 2 ≤ d) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeLinear d (2 ^ m) Q) :
    LargeEvenRecipeLinear d (2 ^ m) fun R _ I F =>
      Q R I F ∧ LargeEvenSimpleGuard (fun R _ I _ => GGInndiagNormal R I) R I F := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  refine ⟨K, inferInstance, inferInstance, hK, hQ, fun _ _ => ?_⟩
  rcases Nat.lt_or_ge d 3 with h3 | h3
  · obtain rfl : d = 2 := by omega
    have := charP_two_of_card hK
    exact ggInndiagNormal_of_subset_inn matConjImage_two_subset_inn
  · exact ggInndiagNormal_linear h3

@[expose] def GGInndiagProvedLabel (lab : LargeEvenLabel) : Prop :=
  GGInndiagInnLabel lab ∨ lab.tag = .A ∨ (lab.tag = .D ∧ lab.rank = 3) ∨
    (lab.tag = .twD ∧ lab.rank = 2)

theorem largeEvenLabelAll_inndiag_proved {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : GGInndiagProvedLabel lab) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => GGInndiagNormal R I) := by
  rcases h with h | h | ⟨h, hl⟩ | ⟨h, hl⟩
  · exact largeEvenLabelAll_inndiag_inn h
  · obtain ⟨t, l, n⟩ := lab
    dsimp only at h
    subst h
    obtain ⟨-, hl1, -⟩ := hlab
    intro Q hQ
    exact recipeLinear_inndiag (by omega) hQ
  · obtain ⟨t, l, n⟩ := lab
    dsimp only at h hl
    subst h hl
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    simp only [↓reduceIte] at hQ ⊢
    exact recipeLinear_inndiag (by omega) hQ
  · obtain ⟨t, l, n⟩ := lab
    dsimp only at h hl
    subst h hl
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    simp only [↓reduceIte] at hQ ⊢
    rw [← pow_mul] at hQ ⊢
    exact recipeLinear_inndiag (by omega) hQ

@[expose] def GGInndiagNormalOtherInput : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → ¬ GGInndiagProvedLabel lab →
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => GGInndiagNormal R I)

theorem ggInndiagNormalInput_of_other (h : GGInndiagNormalOtherInput) : GGInndiagNormalInput := by
  intro lab hlab
  by_cases hi : GGInndiagProvedLabel lab
  · exact largeEvenLabelAll_inndiag_proved hlab hi
  · exact h lab hlab hi

end Labels

end CFSG.StandardType
