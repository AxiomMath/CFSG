module

public import CFSG.LocalAnalysis.StandardType.FF81.CentE6.MatJ
import CFSG.LinearAlgebra.LinearGroups.Generation
import CFSG.Quasithin.Background.GoldschmidtS146PGroups
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import CFSG.Foundations
import CFSG.LieType.SteinbergBROddSylowCore
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherSylow
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
import CFSG.Quasithin.Background.A1cModuleCoprime
import CFSG.Quasithin.Background.A3Components
import CFSG.Quasithin.Background.A3Structure312
import CFSG.Quasithin.Background.OrderingMax
import CFSG.Quasithin.SteinbergOuterPrimeControl
import CFSG.Quasithin.Vol2.Ch1Local
import CFSG.Sporadic.J4Base
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
import CFSG.Walter.Defs
import Certificates.Certificate1
import Certificates.Certificate2
import Certificates.Certificate8026Base

public section

namespace CFSG.StandardType.FF81.CentE6

open scoped MatrixGroups

private def blkIdx (a : Fin 3) : Fin 6 := ⟨a.val + 1, by omega⟩

private def blkIdx' (a : Fin 3) : Fin 6 :=
  if a = 0 then 0 else if a = 1 then 4 else 5

private def blkFun : Fin 3 ⊕ Fin 3 → Fin 6
  | Sum.inl a => blkIdx a
  | Sum.inr a => blkIdx' a

private def blkInvFun (i : Fin 6) : Fin 3 ⊕ Fin 3 :=
  if i = 0 then Sum.inr 0 else if i = 1 then Sum.inl 0 else if i = 2 then Sum.inl 1
    else if i = 3 then Sum.inl 2 else if i = 4 then Sum.inr 1 else Sum.inr 2

private theorem blkFun_leftInverse : Function.LeftInverse blkInvFun blkFun := by
  rintro (a | a) <;> fin_cases a <;> decide

private theorem blkFun_rightInverse : Function.RightInverse blkInvFun blkFun := by
  intro i
  fin_cases i <;> decide

private def blkEquiv : (Fin 3 ⊕ Fin 3) ≃ Fin 6 where
  toFun := blkFun
  invFun := blkInvFun
  left_inv := blkFun_leftInverse
  right_inv := blkFun_rightInverse

private theorem blkEquiv_inl (a : Fin 3) : blkEquiv (Sum.inl a) = blkIdx a := rfl

private theorem blkEquiv_inl_val (a : Fin 3) : (blkEquiv (Sum.inl a)).val = a.val + 1 := rfl

private def blkMatHom : Matrix (Fin 3) (Fin 3) (ZMod 2) →*
    Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  (Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) blkEquiv).toRingEquiv.toMonoidHom.comp
    { toFun := fun A => Matrix.fromBlocks A 0 0 1
      map_one' := Matrix.fromBlocks_one
      map_mul' := by
        intro A B
        rw [Matrix.fromBlocks_multiply]
        simp }

private theorem blkMatHom_apply (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    blkMatHom A = Matrix.reindex blkEquiv blkEquiv (Matrix.fromBlocks A 0 0 1) := by
  rw [blkMatHom]
  rfl

private theorem blkMatHom_inl_inl (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) (p q : Fin 3) :
    (blkMatHom A) (blkEquiv (Sum.inl p)) (blkEquiv (Sum.inl q)) = A p q := by
  simp [blkMatHom_apply, Matrix.reindex_apply, Equiv.symm_apply_apply]

private theorem blkMatHom_inl_inr (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) (p q : Fin 3) :
    (blkMatHom A) (blkEquiv (Sum.inl p)) (blkEquiv (Sum.inr q)) = 0 := by
  simp [blkMatHom_apply, Matrix.reindex_apply, Equiv.symm_apply_apply]

private theorem blkMatHom_inr_inl (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) (p q : Fin 3) :
    (blkMatHom A) (blkEquiv (Sum.inr p)) (blkEquiv (Sum.inl q)) = 0 := by
  simp [blkMatHom_apply, Matrix.reindex_apply, Equiv.symm_apply_apply]

private theorem blkMatHom_inr_inr (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) (p q : Fin 3) :
    (blkMatHom A) (blkEquiv (Sum.inr p)) (blkEquiv (Sum.inr q)) =
      (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) p q := by
  simp [blkMatHom_apply, Matrix.reindex_apply, Equiv.symm_apply_apply]

private theorem det_blkMatHom (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    (blkMatHom A).det = A.det := by
  rw [blkMatHom_apply, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
  simp

private theorem blkMatHom_injective : Function.Injective blkMatHom := by
  intro A B h
  have h' : Matrix.reindex blkEquiv blkEquiv (Matrix.fromBlocks A 0 0 1) =
      Matrix.reindex blkEquiv blkEquiv (Matrix.fromBlocks B 0 0 1) := by
    rw [← blkMatHom_apply, ← blkMatHom_apply]
    exact h
  have h'' : Matrix.fromBlocks A 0 0 1 = Matrix.fromBlocks B 0 0 1 :=
    (Matrix.reindex blkEquiv blkEquiv).injective h'
  ext i j
  have := congrFun (congrFun h'' (Sum.inl i)) (Sum.inl j)
  simpa [Matrix.fromBlocks_apply₁₁] using this

private def blkSLHom : SL(3, ZMod 2) →* SL(6, ZMod 2) where
  toFun A := ⟨blkMatHom (A : Matrix (Fin 3) (Fin 3) (ZMod 2)), by rw [det_blkMatHom, A.2]⟩
  map_one' := by
    apply Subtype.ext
    change blkMatHom (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1
    rw [map_one]
  map_mul' A B := by
    apply Subtype.ext
    change blkMatHom (A.val * B.val) = blkMatHom A.val * blkMatHom B.val
    rw [map_mul]

private theorem blkSLHom_injective : Function.Injective blkSLHom := by
  intro A B h
  apply Subtype.ext
  apply blkMatHom_injective
  exact congrArg (fun g : SL(6, ZMod 2) => (g : Matrix (Fin 6) (Fin 6) (ZMod 2))) h

private theorem coe_elem_ne {a b : Fin 6} (h : a ≠ b) :
    ((elem a b : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      1 + Matrix.single a b 1 := by
  unfold elem
  rw [dif_neg h]
  rfl

private theorem blkSLHom_transvection_one (i j : Fin 3) (hij : i ≠ j) :
    blkSLHom (Matrix.SpecialLinearGroup.transvection hij (1 : ZMod 2)) =
      elem (blkEquiv (Sum.inl i)) (blkEquiv (Sum.inl j)) := by
  apply Subtype.ext
  change blkMatHom (Matrix.SpecialLinearGroup.transvection hij (1 : ZMod 2)).val =
    (elem (blkEquiv (Sum.inl i)) (blkEquiv (Sum.inl j))).val
  apply Matrix.ext
  intro a b
  rw [← Equiv.apply_symm_apply blkEquiv a, ← Equiv.apply_symm_apply blkEquiv b]
  have hne : blkEquiv (Sum.inl i) ≠ blkEquiv (Sum.inl j) :=
    fun h => hij (by simpa using blkEquiv.injective h)
  rcases blkEquiv.symm a with p | p <;> rcases blkEquiv.symm b with q | q
  · rw [blkMatHom_inl_inl, Matrix.SpecialLinearGroup.transvection_coe, coe_elem_ne hne]
    simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, blkEquiv.injective.eq_iff,
      Sum.inl.injEq]
  · rw [blkMatHom_inl_inr, coe_elem_ne hne]
    simp [Matrix.add_apply, blkEquiv.injective.eq_iff, Sum.inl.injEq, Sum.inl_ne_inr]
  · rw [blkMatHom_inr_inl, coe_elem_ne hne]
    simp [Matrix.add_apply, blkEquiv.injective.eq_iff, Sum.inl.injEq, Sum.inl_ne_inr,
      Sum.inr_ne_inl]
  · rw [blkMatHom_inr_inr, coe_elem_ne hne]
    simp [Matrix.add_apply, Matrix.one_apply, blkEquiv.injective.eq_iff, Sum.inr.injEq,
      Sum.inl_ne_inr]

private theorem eq_zero_or_eq_one_zmod_two : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

private theorem closure_blkSLHom_elementary :
    Subgroup.closure (blkSLHom '' CFSG.LinearGroups.elementarySet 3 (ZMod 2)) = Dgrp := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro g ⟨A, hA, rfl⟩
    rcases hA with ⟨i, j, hij, c, rfl⟩
    rcases eq_zero_or_eq_one_zmod_two c with rfl | rfl
    · rw [Matrix.SpecialLinearGroup.transvection_coeff_zero, map_one]
      exact Subgroup.one_mem _
    · rw [blkSLHom_transvection_one i j hij]
      exact Subgroup.subset_closure
        ⟨blkEquiv (Sum.inl i), blkEquiv (Sum.inl j),
          fun h => hij (by simpa using blkEquiv.injective h),
          by rw [blkEquiv_inl_val]; omega, by rw [blkEquiv_inl_val]; omega,
          by rw [blkEquiv_inl_val]; omega, by rw [blkEquiv_inl_val]; omega, rfl⟩
  · rw [Dgrp, Subgroup.closure_le]
    rintro g ⟨i, j, hij, hi1, hi3, hj1, hj3, rfl⟩
    have hi : blkEquiv (Sum.inl ⟨i.val - 1, by omega⟩) = i := by
      rw [blkEquiv_inl]
      apply Fin.ext
      simp only [blkIdx, Fin.val_mk]
      omega
    have hj : blkEquiv (Sum.inl ⟨j.val - 1, by omega⟩) = j := by
      rw [blkEquiv_inl]
      apply Fin.ext
      simp only [blkIdx, Fin.val_mk]
      omega
    have hab : (⟨i.val - 1, by omega⟩ : Fin 3) ≠ ⟨j.val - 1, by omega⟩ := by
      intro h
      apply hij
      exact (hi.symm.trans (congrArg (fun x => blkEquiv (Sum.inl x)) h)).trans hj
    rw [← hi, ← hj, ← blkSLHom_transvection_one _ _ hab]
    exact Subgroup.subset_closure
      ⟨Matrix.SpecialLinearGroup.transvection hab (1 : ZMod 2),
        CFSG.LinearGroups.transvection_mem_elementarySet hab 1, rfl⟩

private theorem blkSLHom_range : blkSLHom.range = Dgrp := by
  rw [MonoidHom.range_eq_map,
    ← CFSG.LinearGroups.special_linear_elementary_generation (K := ZMod 2) (n := 3),
    MonoidHom.map_closure, closure_blkSLHom_elementary]

theorem Dgrp_le_Jgrp : Dgrp ≤ Jgrp := by
  rw [Dgrp, Jgrp]
  apply Subgroup.closure_mono
  rintro g ⟨i, j, hij, hi1, hi3, hj1, hj3, rfl⟩
  exact ⟨i, j, hij, hi1, hi3.trans (by omega), hj1, hj3.trans (by omega), rfl⟩

theorem nonempty_mulEquiv_Dgrp : Nonempty (↥Dgrp ≃* SL(3, ZMod 2)) :=
  ⟨((MonoidHom.ofInjective blkSLHom_injective).trans
    (MulEquiv.subgroupCongr blkSLHom_range)).symm⟩

theorem bStd_mem_Dgrp : bStd ∈ Dgrp := by
  have h12 : elem (1 : Fin 6) 2 ∈ Dgrp :=
    Subgroup.subset_closure ⟨1, 2, by decide, by decide, by decide, by decide, by decide, rfl⟩
  have h21 : elem (2 : Fin 6) 1 ∈ Dgrp :=
    Subgroup.subset_closure ⟨2, 1, by decide, by decide, by decide, by decide, by decide, rfl⟩
  rw [bStd, Dgrp]
  exact Subgroup.mul_mem _ h12 h21

theorem orderOf_bStd : orderOf bStd = 3 :=
  orderOf_eq_prime (by decide +kernel) (by decide +kernel)

end CFSG.StandardType.FF81.CentE6
