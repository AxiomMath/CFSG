module

public import CFSG.LocalAnalysis.StandardType.GGKD2Leaf6D3Contracts
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitarySixThreeFieldAlg

public section

namespace S2MathAs3_1624

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryModel
open Polynomial
open scoped MatrixGroups Polynomial

noncomputable section

theorem cubicFieldBlock_holds : CubicFieldBlockContract := by
  intro K _ _ _ d hd S κ hκ hS3
  classical
  set P : K[X] := Polynomial.X ^ 3 - Polynomial.C (κ : K) with hP
  have hc : ∀ c : K, c ^ 3 ≠ (κ : K) := (noncube_units_iff_field κ).mp hκ
  have hirr : Irreducible P := by
    rw [hP]
    exact TableBU63.irreducible_X_pow_three_sub_C hc
  haveI : Fact (Irreducible P) := ⟨hirr⟩
  have hdeg : P.natDegree = 3 := by
    rw [hP]
    exact natDegree_X_pow_sub_C
  have hP0 : P ≠ 0 := by
    rw [hP]
    exact X_pow_sub_C_ne_zero (by norm_num) (κ : K)
  haveI hfinK : Module.Finite K (AdjoinRoot P) := (AdjoinRoot.powerBasis hP0).finite
  haveI hfinE : Finite (AdjoinRoot P) := Module.finite_of_finite K
  set x : Module.End K (Fin d → K) :=
    Matrix.toLinAlgEquiv' (S : Matrix (Fin d) (Fin d) K) with hx
  have hx3 : x ^ 3 = algebraMap K (Module.End K (Fin d → K)) (κ : K) := by
    have hmat : (S : Matrix (Fin d) (Fin d) K) ^ 3 = Matrix.scalar (Fin d) (κ : K) := by
      rw [← Units.val_pow_eq_pow_val, hS3, Matrix.GeneralLinearGroup.coe_scalar]
    rw [hx, ← map_pow, hmat]
    apply LinearMap.ext
    intro v
    rw [Matrix.toLinAlgEquiv'_apply, Matrix.scalar_apply, Matrix.diagonal_const_mulVec,
      Module.algebraMap_end_apply]
  have hPx : Polynomial.aeval x P = 0 := by
    rw [hP, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hx3, sub_self]
  have htop : KCPrimary.primaryComponent x P = ⊤ := by
    rw [eq_top_iff]
    intro v _
    rw [KCPrimary.mem_primaryComponent, hPx, LinearMap.zero_apply]
  have hd3 : d = 3 * Module.finrank (AdjoinRoot P) (KCPrimary.primaryComponent x P) := by
    have hfr := KCPrimary.finrank_primaryComponent x P
    have htopfr : Module.finrank K (KCPrimary.primaryComponent x P) = d := by
      rw [htop, finrank_top, Module.finrank_fin_fun]
    rw [htopfr, hdeg] at hfr
    exact hfr
  have hm1 : 1 ≤ Module.finrank (AdjoinRoot P) (KCPrimary.primaryComponent x P) := by
    omega
  have hEfr : Module.finrank K (AdjoinRoot P) = 3 := by
    rw [Module.finrank_eq_card_basis (AdjoinRoot.powerBasis hP0).basis, Fintype.card_fin,
      AdjoinRoot.powerBasis_dim hP0, hdeg]
  have hEnat : Nat.card (AdjoinRoot P) = Nat.card K ^ 3 := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := AdjoinRoot P), hEfr]
  have hIsExt : IsCubicExtension K (AdjoinRoot P) := ⟨hfinK, hEfr, hEnat⟩
  have hroot3 : (AdjoinRoot.root P) ^ 3 = algebraMap K (AdjoinRoot P) (κ : K) :=
    TableBU63.root_pow_three (c := (κ : K)) (f := P) hP
  have hadj : Algebra.adjoin K ({AdjoinRoot.root P} : Set (AdjoinRoot P)) = ⊤ := by
    have h := (AdjoinRoot.isAdjoinRoot P).adjoin_root_eq_top
    rwa [AdjoinRoot.isAdjoinRoot_root_eq_root] at h
  set B : Module.Basis (Fin (Module.finrank (AdjoinRoot P) (KCPrimary.primaryComponent x P)))
      (AdjoinRoot P) (KCPrimary.primaryComponent x P) :=
    Module.finBasis (AdjoinRoot P) (KCPrimary.primaryComponent x P) with hB
  set e1 : KCPrimary.primaryComponent x P ≃ₗ[K] (Fin d → K) :=
    LinearEquiv.ofTop (p := KCPrimary.primaryComponent x P) htop with he1
  set e2 : KCPrimary.primaryComponent x P ≃ₗ[K]
      (Fin (Module.finrank (AdjoinRoot P) (KCPrimary.primaryComponent x P)) → AdjoinRoot P) :=
    (B.equivFun).restrictScalars K with he2
  set b : (Fin d → K) ≃ₗ[K]
      (Fin (Module.finrank (AdjoinRoot P) (KCPrimary.primaryComponent x P)) → AdjoinRoot P) :=
    e1.symm.trans e2 with hb
  have hbint : ∀ v : Fin d → K,
      b ((S : Matrix (Fin d) (Fin d) K).mulVec v) = AdjoinRoot.root P • b v := by
    intro v
    have hroot : e1.symm ((S : Matrix (Fin d) (Fin d) K).mulVec v) =
        AdjoinRoot.root P • e1.symm v := by
      apply e1.injective
      rw [he1, LinearEquiv.apply_symm_apply, LinearEquiv.ofTop_apply,
        KCPrimary.coe_root_smul_primaryComponent, LinearEquiv.coe_ofTop_symm_apply,
        hx, Matrix.toLinAlgEquiv'_apply]
    have hbv : b ((S : Matrix (Fin d) (Fin d) K).mulVec v) =
        e2 (e1.symm ((S : Matrix (Fin d) (Fin d) K).mulVec v)) := by
      rw [hb]
      rfl
    have hb0 : b v = e2 (e1.symm v) := by
      rw [hb]
      rfl
    rw [hbv, hb0, hroot, he2]
    change B.equivFun (AdjoinRoot.root P • e1.symm v) =
      AdjoinRoot.root P • B.equivFun (e1.symm v)
    rw [map_smul]
  refine ⟨Module.finrank (AdjoinRoot P) (KCPrimary.primaryComponent x P), AdjoinRoot P,
    inferInstance, inferInstance, inferInstance, hm1, hd3, hIsExt, hirr,
    AdjoinRoot.root P, hroot3, hadj, b, hbint⟩

end

end S2MathAs3_1624

end
