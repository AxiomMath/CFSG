module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeBlock
public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutMain
public import CFSG.ClassicalInvolution.Balance.StrongPowSuBlocks
import CFSG.LocalAnalysis.StandardType.GGQTwoDGNUnitGen
import CFSG.LocalAnalysis.StandardType.GGSuNsRootGenComp
import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSUBlock
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
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.StandardType

namespace SuNsRootGen

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K] {n d : ℕ}

theorem coordBlockSU_map_suEquivUnitarySU [Finite K] [CharP K 2] (hK : Nat.card K = (2 ^ n) ^ 2)
    (S : Finset (Fin d)) :
    (coordBlockSU K 2 n S).map (suEquivUnitarySU K 2 n hK d).toMonoidHom =
      TableBUE.blockSU (K := K) (n := n) S := by
  ext y
  rw [Subgroup.mem_map_equiv, mem_coordBlockSU_iff, TableBUE.mem_blockSU]
  simp only [coe_suEquivUnitarySU_symm, TableBUE.IsBlockOn, Matrix.one_apply]

theorem iSup_blockSU_triples (h : UnitaryFieldData 2 1 K) (hd : 4 ≤ d) :
    (⨆ (S : Finset (Fin d)) (_ : S.card = 3), TableBUE.blockSU (K := K) (n := 1) S) = ⊤ := by
  have := h.finite
  have := h.charP
  have key := congrArg (Subgroup.map (suEquivUnitarySU K 2 1 h.card_eq_sq d).toMonoidHom)
    (QTwo.iSup_coordBlockSU_card_three_eq_top (h.card.trans (by norm_num)) hd)
  simpa only [Subgroup.map_iSup, coordBlockSU_map_suEquivUnitarySU,
    Subgroup.map_top_of_surjective (suEquivUnitarySU K 2 1 h.card_eq_sq d).toMonoidHom
      (suEquivUnitarySU K 2 1 h.card_eq_sq d).surjective] using key

theorem iSup_blockSU_card_three_eq_top (h : UnitaryFieldData 2 n K) (hd : 3 ≤ d) :
    (⨆ (S : Finset (Fin d)) (_ : S.card = 3), TableBUE.blockSU (K := K) (n := n) S) = ⊤ := by
  rcases hd.eq_or_lt with rfl | hd4
  · rw [eq_top_iff, ← SUTorus.blockSU_univ (K := K) (f := n)]
    exact le_iSup₂_of_le Finset.univ (by simp) le_rfl
  rcases h.one_le.eq_or_lt with rfl | hn
  · exact iSup_blockSU_triples h hd4
  have hq : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine top_le_iff.mp ?_
  rw [← iSup_blockSU_pairs h hq hd ⟨0, by omega⟩ ⟨0, by omega⟩]
  refine iSup₂_le fun i j => iSup_le fun hij => ?_
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({i, j} : Finset (Fin d))) (t := Finset.univ)
    (by rw [Finset.card_univ, Fintype.card_fin]; exact Finset.card_le_two.trans_lt (by omega))
  refine (SUTorus.blockSU_mono (Finset.subset_insert k _)).trans
    (le_iSup₂_of_le (insert k {i, j}) ?_ le_rfl)
  rw [Finset.card_insert_of_notMem hk, Finset.card_pair hij.1]

end SuNsRootGen

end CFSG.StandardType
