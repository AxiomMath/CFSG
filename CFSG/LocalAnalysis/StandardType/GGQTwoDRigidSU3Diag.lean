module

public import CFSG.ClassicalInvolution.Balance.StrongPowSuBlocks
import CFSG.ClassicalInvolution.Balance.StrongPowSuDiag
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.ClassicalInvolution.Balance.PassTwoFinal
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieClassical
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieE6E7Triality
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank
import CFSG.ClassicalInvolution.Models.UnitaryPairs
import CFSG.ClassicalInvolution.Models.UnitaryPairs.Pairs

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.ClassicalInvolution.RouteD.Gaps (diagGL coe_diagGL coe_diagGL_inv
  exists_diagGL_of_offdiag_zero)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (unitLambdaDiag unitLambdaDiag_mem
  unitSignedSwapMatrix unitSignedSwapMatrix_mem)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
private theorem unit_pow_three (hK : Nat.card K = 4) (u : Kˣ) : u ^ 3 = 1 := by
  have hun : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
  have h := pow_card_eq_one' (x := u)
  simpa [hun] using h

omit [Finite K] [CharP K 2] in
theorem cube_eq_one_of_ne_zero (hK : Nat.card K = 4) {x : K} (hx : x ≠ 0) :
    x ^ 3 = 1 := by
  have h := congrArg (fun u : Kˣ => (u : K)) (unit_pow_three hK (Units.mk0 x hx))
  simpa [Units.val_pow_eq_pow_val, Units.val_mk0] using h

theorem diagGL_mem_SUid (hK : Nat.card K = 4) {d : Fin 3 → Kˣ}
    (hdet : (∏ i, (d i : K)) = 1) :
    diagGL d ∈ SUid (unitaryInvolution K 2 1) 3 := by
  refine ⟨?_, ?_⟩
  · rw [coe_diagGL, Matrix.det_diagonal, hdet]
  · rw [coe_diagGL, conjTr, Matrix.diagonal_map (map_zero (unitaryInvolution K 2 1)),
      Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [unitaryInvolution_apply, pow_one, ← pow_succ]
    exact cube_eq_one_of_ne_zero hK (d i).ne_zero

omit [Finite K] [CharP K 2] in
private theorem diagGL_pow_three_eq_one (hK : Nat.card K = 4) (d : Fin 3 → Kˣ) :
    (diagGL d) ^ 3 = 1 := by
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, Units.val_one, coe_diagGL, Matrix.diagonal_pow,
    ← Matrix.diagonal_one]
  congr 1
  funext i
  change ((d i : K) ^ 3) = 1
  rw [← Units.val_pow_eq_pow_val, unit_pow_three hK (d i), Units.val_one]

theorem diagGL_mem_coordBlockSU (hK : Nat.card K = 4) {J : Finset (Fin 3)}
    {d : Fin 3 → Kˣ} (hdet : (∏ i, (d i : K)) = 1) (hd : ∀ i, i ∉ J → d i = 1) :
    (⟨diagGL d, diagGL_mem_SUid hK hdet⟩ : Su K 2 1 3) ∈ coordBlockSU K 2 1 J := by
  rw [mem_coordBlockSU_iff]
  intro i j hij
  change ((diagGL d : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j = _
  rw [coe_diagGL, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h
    have hi : i ∉ J := by rcases hij with h | h <;> exact h
    simp [hd i hi]
  · simp [h]

@[expose]
def diagSub : Subgroup (Su K 2 1 3) where
  carrier := {g | ∀ i j : Fin 3, i ≠ j →
    (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) i j = 0}
  one_mem' := by
    intro i j hij
    simp [hij]
  mul_mem' := by
    intro a b ha hb i j hij
    rw [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k = i
    · subst hk
      rw [hb k j hij, mul_zero]
    · rw [ha i k (Ne.symm hk), zero_mul]
  inv_mem' := by
    intro a ha i j hij
    have hmul : (((a * a⁻¹ : Su K 2 1 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
      have h : (a : GL (Fin 3) K) * ((a⁻¹ : Su K 2 1 3) : GL (Fin 3) K) = 1 := by
        simp
      simp
    have h := congrFun (congrFun hmul i) j
    simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply, Matrix.one_apply] at h
    have h2 : (((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) i i *
        (((a⁻¹ : Su K 2 1 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
      rw [Finset.sum_eq_single i] at h
      · simpa [hij] using h
      · intro k _ hk
        rw [ha i k (Ne.symm hk), zero_mul]
      · intro hi
        simp at hi
    have hdiag := congrFun (congrFun hmul i) i
    simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply, Matrix.one_apply] at hdiag
    have hii : (((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) i i ≠ 0 := by
      have h3 : (((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) i i *
          (((a⁻¹ : Su K 2 1 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i i = 1 := by
        rw [Finset.sum_eq_single i] at hdiag
        · simpa using hdiag
        · intro k _ hk
          rw [ha i k (Ne.symm hk), zero_mul]
        · intro hi
          simp at hi
      rintro hzero
      rw [hzero, zero_mul] at h3
      exact zero_ne_one h3
    exact (mul_eq_zero.mp h2).resolve_left hii

theorem diagSub_pow_three (hK : Nat.card K = 4) {a : Su K 2 1 3}
    (ha : a ∈ diagSub) : a ^ 3 = 1 := by
  obtain ⟨d, hd⟩ := exists_diagGL_of_offdiag_zero (a : GL (Fin 3) K) ha
  refine Subtype.ext (Units.ext ?_)
  rw [Subgroup.coe_pow, hd, diagGL_pow_three_eq_one hK d]
  rfl


end CFSG.StandardType.QTwo

end
