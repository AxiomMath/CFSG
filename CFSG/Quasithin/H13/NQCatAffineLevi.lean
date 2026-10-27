module

public import CFSG.Quasithin.H13.NQCatAffineCore
public import CFSG.LieType.SteinbergBROddLinearThreeParabolic

public section

namespace CFSG.Quasithin.H13.NQCat

open Subgroup CFSG.LieType.SteinbergBR.BlockPar CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem chiL_surjective {F : Type*} [Field F] {a : Type*} [Fintype a] [DecidableEq a] :
    Function.Surjective (chiL F a (Fin 1)) := by
  intro A
  let E : Matrix (Fin 1) (Fin 1) F :=
    Matrix.diagonal fun _ => (((Matrix.GeneralLinearGroup.det A)⁻¹ : Fˣ) : F)
  let g : Matrix.SpecialLinearGroup (a ⊕ Fin 1) F := ⟨Matrix.fromBlocks A.val 0 0 E, by
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_diagonal, Fin.prod_univ_one,
      ← Matrix.GeneralLinearGroup.val_det_apply, Units.mul_inv]⟩
  refine ⟨⟨g, Matrix.toBlocks_fromBlocks₂₁ _ _ _ _⟩, Units.ext ?_⟩
  exact Matrix.toBlocks_fromBlocks₁₁ _ _ _ _

theorem chiR_surjective {F : Type*} [Field F] {b : Type*} [Fintype b] [DecidableEq b] :
    Function.Surjective (chiR F (Fin 1) b) := by
  intro A
  let E : Matrix (Fin 1) (Fin 1) F :=
    Matrix.diagonal fun _ => (((Matrix.GeneralLinearGroup.det A)⁻¹ : Fˣ) : F)
  let g : Matrix.SpecialLinearGroup (Fin 1 ⊕ b) F := ⟨Matrix.fromBlocks E 0 0 A.val, by
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_diagonal, Fin.prod_univ_one,
      ← Matrix.GeneralLinearGroup.val_det_apply, Units.inv_mul]⟩
  refine ⟨⟨g, Matrix.toBlocks_fromBlocks₂₁ _ _ _ _⟩, Units.ext ?_⟩
  exact Matrix.toBlocks_fromBlocks₂₂ _ _ _ _

theorem eq_one_of_det_eq_one_fin_one {F : Type*} [Field F] {M : Matrix (Fin 1) (Fin 1) F}
    (h : M.det = 1) : M = 1 := by
  rw [Matrix.det_unique] at h
  ext i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  simpa using h

theorem levi_nat {F : Type*} [Field F] {s : Matrix.SpecialLinearGroup (Fin 3) F}
    {W : Submodule F (Fin 3 → F)} (hs : (flagSpace 3 F 2).map (Matrix.mulVecLin s.val) = W) :
    ∃ (ρ : ↥(stabilizer W) →* GL (Fin 2) F) (hθQ : (natTheta F s).range ≤ stabilizer W),
      Function.Surjective ρ ∧
      (∀ x, ρ ⟨natTheta F s x, hθQ ⟨x, rfl⟩⟩ = Matrix.SpecialLinearGroup.toGL x.right) ∧
      ∀ g : ↥(stabilizer W), ρ g = 1 →
        (g : Matrix.SpecialLinearGroup (Fin 3) F) ∈
          ((natTheta F s).comp SemidirectProduct.inl).range := by
  have h : 2 + 1 = 3 := rfl
  let e := parQEquiv h hs
  have hθQ : (natTheta F s).range ≤ stabilizer W := by
    rintro _ ⟨x, rfl⟩
    exact (mem_parQ_iff_transport h hs (thetaL F (Fin 2) (Fin 1) x)).mp
      (parJL_le_parQ ⟨x, rfl⟩)
  refine ⟨(chiL F (Fin 2) (Fin 1)).comp e.symm.toMonoidHom, hθQ,
    chiL_surjective.comp e.symm.surjective, fun x => ?_, fun g hg => ?_⟩
  · have he : e.symm ⟨natTheta F s x, hθQ ⟨x, rfl⟩⟩ =
        ⟨thetaL F (Fin 2) (Fin 1) x, parJL_le_parQ ⟨x, rfl⟩⟩ := by
      rw [MulEquiv.symm_apply_eq]
      exact Subtype.ext rfl
    change chiL F (Fin 2) (Fin 1) (e.symm ⟨natTheta F s x, hθQ ⟨x, rfl⟩⟩) = _
    rw [he]
    apply Units.ext
    change (thetaL F (Fin 2) (Fin 1) x).val.toBlocks₁₁ = x.right.val
    rw [thetaL_val, Matrix.toBlocks_fromBlocks₁₁]
  · set M := e.symm g with hM
    have hM1 : (M : Matrix.SpecialLinearGroup (Fin 2 ⊕ Fin 1) F).val.toBlocks₁₁ = 1 :=
      congrArg Units.val hg
    have hdet := det_eq_of_mem_parQ M.2
    rw [hM1, Matrix.det_one, one_mul] at hdet
    have hM2 := eq_one_of_det_eq_one_fin_one hdet
    have hMval : (M : Matrix.SpecialLinearGroup (Fin 2 ⊕ Fin 1) F).val = Matrix.fromBlocks 1
        (M : Matrix.SpecialLinearGroup (Fin 2 ⊕ Fin 1) F).val.toBlocks₁₂ 0 1 := by
      rw [← hM1, ← hM2]
      exact eq_fromBlocks_of_mem_parQ M.2
    have hg' : (g : Matrix.SpecialLinearGroup (Fin 3) F) =
        transportSL F h s (M : Matrix.SpecialLinearGroup (Fin 2 ⊕ Fin 1) F) :=
      (congrArg Subtype.val (e.apply_symm_apply g)).symm
    refine ⟨Multiplicative.ofAdd (M : Matrix.SpecialLinearGroup (Fin 2 ⊕ Fin 1) F).val.toBlocks₁₂,
      ?_⟩
    rw [hg']
    change transportSL F h s (thetaL F (Fin 2) (Fin 1) (SemidirectProduct.inl _)) = _
    congr 1
    apply Subtype.ext
    rw [thetaL_val]
    conv_rhs => rw [hMval]
    simp only [SemidirectProduct.left_inl, SemidirectProduct.right_inl,
      Matrix.SpecialLinearGroup.coe_one, toAdd_ofAdd]

theorem levi_dual {F : Type*} [Field F] {s : Matrix.SpecialLinearGroup (Fin 3) F}
    {W : Submodule F (Fin 3 → F)} (hs : (flagSpace 3 F 1).map (Matrix.mulVecLin s.val) = W) :
    ∃ (ρ : ↥(stabilizer W) →* GL (Fin 2) F) (hθQ : (dualTheta F s).range ≤ stabilizer W),
      Function.Surjective ρ ∧
      (∀ x, ρ ⟨dualTheta F s x, hθQ ⟨x, rfl⟩⟩ = Matrix.SpecialLinearGroup.toGL x.right) ∧
      ∀ g : ↥(stabilizer W), ρ g = 1 →
        (g : Matrix.SpecialLinearGroup (Fin 3) F) ∈
          ((dualTheta F s).comp SemidirectProduct.inl).range := by
  have h : 1 + 2 = 3 := rfl
  let e := parQEquiv h hs
  have hθQ : (dualTheta F s).range ≤ stabilizer W := by
    rintro _ ⟨x, rfl⟩
    exact (mem_parQ_iff_transport h hs (thetaR F (Fin 1) (Fin 2) x)).mp
      (parJR_le_parQ ⟨x, rfl⟩)
  refine ⟨(chiR F (Fin 1) (Fin 2)).comp e.symm.toMonoidHom, hθQ,
    chiR_surjective.comp e.symm.surjective, fun x => ?_, fun g hg => ?_⟩
  · have he : e.symm ⟨dualTheta F s x, hθQ ⟨x, rfl⟩⟩ =
        ⟨thetaR F (Fin 1) (Fin 2) x, parJR_le_parQ ⟨x, rfl⟩⟩ := by
      rw [MulEquiv.symm_apply_eq]
      exact Subtype.ext rfl
    change chiR F (Fin 1) (Fin 2) (e.symm ⟨dualTheta F s x, hθQ ⟨x, rfl⟩⟩) = _
    rw [he]
    apply Units.ext
    change (thetaR F (Fin 1) (Fin 2) x).val.toBlocks₂₂ = x.right.val
    rw [thetaR_val, Matrix.toBlocks_fromBlocks₂₂]
  · set M := e.symm g with hM
    have hM2 : (M : Matrix.SpecialLinearGroup (Fin 1 ⊕ Fin 2) F).val.toBlocks₂₂ = 1 :=
      congrArg Units.val hg
    have hdet := det_eq_of_mem_parQ M.2
    rw [hM2, Matrix.det_one, mul_one] at hdet
    have hM1 := eq_one_of_det_eq_one_fin_one hdet
    have hMval : (M : Matrix.SpecialLinearGroup (Fin 1 ⊕ Fin 2) F).val = Matrix.fromBlocks 1
        (M : Matrix.SpecialLinearGroup (Fin 1 ⊕ Fin 2) F).val.toBlocks₁₂ 0 1 := by
      rw [← hM1, ← hM2]
      exact eq_fromBlocks_of_mem_parQ M.2
    have hg' : (g : Matrix.SpecialLinearGroup (Fin 3) F) =
        transportSL F h s (M : Matrix.SpecialLinearGroup (Fin 1 ⊕ Fin 2) F) :=
      (congrArg Subtype.val (e.apply_symm_apply g)).symm
    refine ⟨Multiplicative.ofAdd (M : Matrix.SpecialLinearGroup (Fin 1 ⊕ Fin 2) F).val.toBlocks₁₂,
      ?_⟩
    rw [hg']
    change transportSL F h s (thetaR F (Fin 1) (Fin 2) (SemidirectProduct.inl _)) = _
    congr 1
    apply Subtype.ext
    rw [thetaR_val]
    conv_rhs => rw [hMval]
    simp only [SemidirectProduct.left_inl, SemidirectProduct.right_inl,
      Matrix.SpecialLinearGroup.coe_one, toAdd_ofAdd, Matrix.mul_one]

theorem phiL_transitive {F : Type*} [Field F]
    (n m : Multiplicative (Matrix (Fin 2) (Fin 1) F)) (hn : n ≠ 1) (hm : m ≠ 1) :
    ∃ A, phiL F (Fin 1) A n = m := by
  obtain ⟨A, hA⟩ := exists_SL2_mul_eq (X := Multiplicative.toAdd n) (Y := Multiplicative.toAdd m)
    (fun h => hn (Multiplicative.toAdd.injective (h.trans toAdd_one.symm)))
    (fun h => hm (Multiplicative.toAdd.injective (h.trans toAdd_one.symm)))
  refine ⟨A, Multiplicative.toAdd.injective ?_⟩
  change A.val * Multiplicative.toAdd n = Multiplicative.toAdd m
  exact hA

theorem phiR_transitive {F : Type*} [Field F]
    (n m : Multiplicative (Matrix (Fin 1) (Fin 2) F)) (hn : n ≠ 1) (hm : m ≠ 1) :
    ∃ A, phiR F (Fin 1) A n = m := by
  obtain ⟨A, hA⟩ := exists_SL2_row_mul_eq (X := Multiplicative.toAdd n)
    (Y := Multiplicative.toAdd m)
    (fun h => hn (Multiplicative.toAdd.injective (h.trans toAdd_one.symm)))
    (fun h => hm (Multiplicative.toAdd.injective (h.trans toAdd_one.symm)))
  refine ⟨A, Multiplicative.toAdd.injective ?_⟩
  change Multiplicative.toAdd n * (A⁻¹).val = Multiplicative.toAdd m
  exact hA

theorem pow_char_multiplicative_matrix {F : Type*} [Field F] {p : ℕ} [CharP F p] {a b : ℕ}
    (x : Multiplicative (Matrix (Fin a) (Fin b) F)) : x ^ p = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one, ← Nat.cast_smul_eq_nsmul F, CharP.cast_eq_zero, zero_smul]

end CFSG.Quasithin.H13.NQCat
