module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUStd
public import CFSG.LieType.Universal.Unitary.Basic
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Families
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAut
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.LieType.Ree.LargeReeSylowOpposition
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.RankThree.PartOne.KE.A1Action
public import CFSG.RankThree.PartOne.KE.A1Levi
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A1TwistedE6
public import CFSG.RankThree.PartOne.KE.SLnShape
public import CFSG.RankThree.PartOne.KE.SigmaPerX
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KGD.D4Frame
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.Walter.Defs

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.Universal.Unitary
open scoped MatrixGroups Matrix

section Mat

variable {L : Type} [Field L] [CharP L 2]

private theorem excU7Cover_mul_transvection_01_45 (c c' : L) :
    ((Matrix.SpecialLinearGroup.transvection (show (0 : Fin 6) ≠ 1 by decide) c *
        Matrix.SpecialLinearGroup.transvection (show (4 : Fin 6) ≠ 5 by decide) c' :
        SL(6, L)) : Matrix (Fin 6) (Fin 6) L) =
      1 + Matrix.single (0 : Fin 6) (1 : Fin 6) c +
        Matrix.single (4 : Fin 6) (5 : Fin 6) c' := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.SpecialLinearGroup.transvection_coe]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.single_mul_single_of_ne _ _ _ _ (by decide : (1 : Fin 6) ≠ 4)]
  abel

theorem excU7Cover_frob_self (σ : L ≃+* L) (g : SL(6, L))
    (hg : ((g : Matrix (Fin 6) (Fin 6) L).map σ)ᵀ * (g : Matrix (Fin 6) (Fin 6) L) = antidiag 6) :
    ∃ J : SL(6, L), (J : Matrix (Fin 6) (Fin 6) L) = antidiag 6 ∧
      stdUnitary σ.toRingHom g = g * J := by
  classical
  let M : Matrix (Fin 6) (Fin 6) L := (g : Matrix (Fin 6) (Fin 6) L)
  let J0 : Matrix (Fin 6) (Fin 6) L := antidiag 6
  let A : Matrix (Fin 6) (Fin 6) L := (M.map σ.toRingHom)ᵀ
  have hdet : M.det = 1 := Matrix.SpecialLinearGroup.det_coe g
  have hAM : A * M = J0 := hg
  have hJJ : J0 * J0 = 1 := antidiag_mul_self 6
  have hMinv : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M (by rw [hdet]; exact isUnit_one)
  have hAinv : A⁻¹ = M * J0 := by
    refine Matrix.inv_eq_right_inv ?_
    calc A * (M * J0) = (A * M) * J0 := by rw [Matrix.mul_assoc]
      _ = J0 * J0 := by rw [hAM]
      _ = 1 := hJJ
  have hmap : (((M.map σ.toRingHom)⁻¹)ᵀ) = A⁻¹ := by
    rw [Matrix.transpose_nonsing_inv]
  refine ⟨g⁻¹ * stdUnitary σ.toRingHom g, ?_, ?_⟩
  · rw [Matrix.SpecialLinearGroup.coe_mul, coe_stdUnitary,
      CFSG.RankThree.Classical2.coe_inv_eq_nonsing_inv, hmap, hAinv]
    change M⁻¹ * (M * J0) = J0
    rw [← Matrix.mul_assoc, hMinv, Matrix.one_mul]
  · group

theorem excU7Cover_J_conj_10 (J : SL(6, L)) (hJ : (J : Matrix (Fin 6) (Fin 6) L) = antidiag 6)
    (s : L) :
    J * Matrix.SpecialLinearGroup.transvection (show (1 : Fin 6) ≠ 0 by decide) s * J⁻¹ =
      Matrix.SpecialLinearGroup.transvection (show (4 : Fin 6) ≠ 5 by decide) s := by
  have hJJ : J * J = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, hJ, antidiag_mul_self]
    exact Matrix.SpecialLinearGroup.coe_one.symm
  have hJinv : J⁻¹ = J := inv_eq_of_mul_eq_one_right hJJ
  apply Subtype.ext
  rw [hJinv, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    hJ, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.SpecialLinearGroup.transvection_coe]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    antidiag_mul_self, antidiag_mul_single, single_mul_antidiag,
    show (Fin.rev (1 : Fin 6)) = 4 by decide,
    show (Fin.rev (0 : Fin 6)) = 5 by decide]

theorem excU7Cover_J_conj_54 (J : SL(6, L)) (hJ : (J : Matrix (Fin 6) (Fin 6) L) = antidiag 6)
    (s : L) :
    J * Matrix.SpecialLinearGroup.transvection (show (5 : Fin 6) ≠ 4 by decide) s * J⁻¹ =
      Matrix.SpecialLinearGroup.transvection (show (0 : Fin 6) ≠ 1 by decide) s := by
  have hJJ : J * J = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, hJ, antidiag_mul_self]
    exact Matrix.SpecialLinearGroup.coe_one.symm
  have hJinv : J⁻¹ = J := inv_eq_of_mul_eq_one_right hJJ
  apply Subtype.ext
  rw [hJinv, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    hJ, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.SpecialLinearGroup.transvection_coe]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    antidiag_mul_self, antidiag_mul_single, single_mul_antidiag,
    show (Fin.rev (5 : Fin 6)) = 0 by decide,
    show (Fin.rev (4 : Fin 6)) = 1 by decide]

theorem excU7Cover_frob_conj_01 (σ : L ≃+* L) (g J : SL(6, L))
    (hJ : (J : Matrix (Fin 6) (Fin 6) L) = antidiag 6) (hg : stdUnitary σ.toRingHom g = g * J)
    (t : L) :
    stdUnitary σ.toRingHom
        (g * Matrix.SpecialLinearGroup.transvection (show (0 : Fin 6) ≠ 1 by decide) t * g⁻¹) =
      g * Matrix.SpecialLinearGroup.transvection (show (4 : Fin 6) ≠ 5 by decide) (σ t) * g⁻¹ := by
  calc
    stdUnitary σ.toRingHom
        (g * Matrix.SpecialLinearGroup.transvection (show (0 : Fin 6) ≠ 1 by decide) t * g⁻¹)
        = (g * J) *
            Matrix.SpecialLinearGroup.transvection (show (1 : Fin 6) ≠ 0 by decide) (-(σ t)) *
            (g * J)⁻¹ := by
          rw [map_mul, map_mul, map_inv, hg,
            stdUnitary_transvection σ.toRingHom (show (0 : Fin 6) ≠ 1 by decide) t]
          rfl
    _ = g * (J * Matrix.SpecialLinearGroup.transvection
            (show (1 : Fin 6) ≠ 0 by decide) (-(σ t)) * J⁻¹) * g⁻¹ := by
          group
    _ = g * Matrix.SpecialLinearGroup.transvection
            (show (4 : Fin 6) ≠ 5 by decide) (-(σ t)) * g⁻¹ := by
          rw [excU7Cover_J_conj_10 J hJ (-(σ t))]
    _ = g * Matrix.SpecialLinearGroup.transvection
            (show (4 : Fin 6) ≠ 5 by decide) (σ t) * g⁻¹ := by
          rw [CharTwo.neg_eq]

theorem excU7Cover_frob_conj_45 (σ : L ≃+* L) (g J : SL(6, L))
    (hJ : (J : Matrix (Fin 6) (Fin 6) L) = antidiag 6) (hg : stdUnitary σ.toRingHom g = g * J)
    (t : L) :
    stdUnitary σ.toRingHom
        (g * Matrix.SpecialLinearGroup.transvection (show (4 : Fin 6) ≠ 5 by decide) t * g⁻¹) =
      g * Matrix.SpecialLinearGroup.transvection (show (0 : Fin 6) ≠ 1 by decide) (σ t) * g⁻¹ := by
  calc
    stdUnitary σ.toRingHom
        (g * Matrix.SpecialLinearGroup.transvection (show (4 : Fin 6) ≠ 5 by decide) t * g⁻¹)
        = (g * J) *
            Matrix.SpecialLinearGroup.transvection (show (5 : Fin 6) ≠ 4 by decide) (-(σ t)) *
            (g * J)⁻¹ := by
          rw [map_mul, map_mul, map_inv, hg,
            stdUnitary_transvection σ.toRingHom (show (4 : Fin 6) ≠ 5 by decide) t]
          rfl
    _ = g * (J * Matrix.SpecialLinearGroup.transvection
            (show (5 : Fin 6) ≠ 4 by decide) (-(σ t)) * J⁻¹) * g⁻¹ := by
          group
    _ = g * Matrix.SpecialLinearGroup.transvection
            (show (0 : Fin 6) ≠ 1 by decide) (-(σ t)) * g⁻¹ := by
          rw [excU7Cover_J_conj_54 J hJ (-(σ t))]
    _ = g * Matrix.SpecialLinearGroup.transvection
            (show (0 : Fin 6) ≠ 1 by decide) (σ t) * g⁻¹ := by
          rw [CharTwo.neg_eq]

theorem excU7Cover_commute_01_45 (s t : L) :
    Commute (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 6) ≠ 1 by decide) s)
      (Matrix.SpecialLinearGroup.transvection (show (4 : Fin 6) ≠ 5 by decide) t) := by
  exact Matrix.SpecialLinearGroup.commute_transvection (i := 0) (j := 1) (k := 4) (l := 5)
    (by decide) (by decide) (by decide) (by decide) s t

theorem excU7Cover_mat_split (g X : SL(6, L)) (c c' : L)
    (hX : (X : Matrix (Fin 6) (Fin 6) L) =
      (g : Matrix (Fin 6) (Fin 6) L) *
        (1 + Matrix.single (0 : Fin 6) (1 : Fin 6) c + Matrix.single (4 : Fin 6) (5 : Fin 6) c') *
        ((g⁻¹ : SL(6, L)) : Matrix (Fin 6) (Fin 6) L)) :
    X = (g * Matrix.SpecialLinearGroup.transvection (show (0 : Fin 6) ≠ 1 by decide) c * g⁻¹) *
      (g * Matrix.SpecialLinearGroup.transvection (show (4 : Fin 6) ≠ 5 by decide) c' * g⁻¹) := by
  have hX' : X = g * (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 6) ≠ 1 by decide) c *
      Matrix.SpecialLinearGroup.transvection (show (4 : Fin 6) ≠ 5 by decide) c') * g⁻¹ := by
    apply Subtype.ext
    rw [hX, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      excU7Cover_mul_transvection_01_45,
      CFSG.RankThree.Classical2.coe_inv_eq_nonsing_inv]
  rw [hX']
  group

end Mat

end CFSG.StandardType.LieKnownR2.ExcPos
