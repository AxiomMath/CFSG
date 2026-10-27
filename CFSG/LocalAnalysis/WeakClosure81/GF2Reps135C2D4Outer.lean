module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2ExcCommon
public import CFSG.Quasithin.Background.SmithB45D4
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2D4Index
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2D4OuterAct
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Ctx
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135Ctx
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.ClassicalGroups
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.GH74.BNPair.Defs
public import CFSG.GH74.GLS.IVK.L2.F1
public import CFSG.GH74.KGroups.L3EpsNoNormalThree
public import CFSG.GH74.KGroups.L3EpsOutExp
public import CFSG.GH74.KGroups.L3EpsOuterLin
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeCore
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeUnitary
public import CFSG.LieType.SeitzGeneration.UnitaryBlocks
public import CFSG.LieType.SeitzGeneration.UnitaryHyperScope
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Bounded
public import CFSG.LocalAnalysis.SectionRank.QTK.EvenOrth
public import CFSG.LocalAnalysis.SectionRank.QTK.Exc
public import CFSG.LocalAnalysis.SectionRank.QTK.OddOrth
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20b
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveDefs
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135Defs
public import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.OddKernel.CompleteRankComparison
public import CFSG.RankThree.PartOne.KF.ClsPSL
public import CFSG.RankThree.PartOne.KF.SU5Model
public import CFSG.RankThree.PartOne.KF.SymCtxMatrix
public import CFSG.RankThree.PartOne.KF.ToralQuot
public import CFSG.RankThree.PartOne.KF.UnitaryModel
public import CFSG.RankThree.PartOne.S11c.Sec66PSL
public import CFSG.RankThree.PartOne.S11c.Sec66Sp
public import CFSG.RankThree.PartOne.S11c.SuFiveD
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutUnitary
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.Sporadic.Recognition.JankoWongPSLNine
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Gen

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4
open CFSG.Quasithin.B42D4 CFSG.Quasithin.B42Disp CFSG.Quasithin.B45Disp


variable {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)} {t : MulAut W}
variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ f) ^ 3)
  (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
  (e : ↥L ⧸ Subgroup.center ↥L ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom)

local notation "C₀" => graphFixedRootGroup TwistTag.D4 K σ.toRingHom
local notation "Xr" => pinnedX TwistTag.D4.tag K

include hf hK hσ e in
theorem w135c2_trialityD4_outer (hW : ∀ w : W, w ^ 2 = 1) (hctx : Is135Context Y L)
    (hZL : Subgroup.center ↥L = ⊥) (htY : t ∈ Y) (ht2 : orderOf t = 2) (htL : t ∉ L) :
    4 ≤ E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) := by
  have hV : ∀ v : W, v * v = 1 := fun v => by rw [← pow_two]; exact hW v
  have hN := w135c2_mem_normalizer_of_ctx hctx htY ht2
  let x : Subgroup.normalizer (L : Set (MulAut W)) := ⟨t, hN⟩
  have hx2 : (x : MulAut W) * x = 1 := by
    change t * t = 1
    rw [← sq, ← ht2]
    exact pow_orderOf_eq_one t
  let α : MulAut C₀ := modelAct L e x
  have hα : α * α = 1 := by
    dsimp only [α]
    exact w135c2_modelAct_sq hctx e htY ht2 hN
  have hαo : α ∉ (MulAut.conj : C₀ →* MulAut C₀).range := by
    rintro ⟨c, hc⟩
    exact w135c2_modelAct_not_inner hctx hZL e htY ht2 htL hN c hc.symm
  obtain ⟨-, hdisp⟩ := CFSG.Quasithin.B45D4.dispAtOut_outer hf hK σ hσ α hα hαo
  have hDQ : DoubleDispOut L (CFSG.Quasithin.B45D4.outerPrimes f) :=
    CFSG.Quasithin.B45Tor.doubleDispOut_trialityD4 hf hK σ hσ hV L hZL e
  have hlt := sq_lt_index_of_dispAtOut L hctx.2.2.2.2.1.1 hZL e
    (Q := CFSG.Quasithin.B45D4.outerPrimes f) hDQ x hx2 hdisp
  have hpow : (2 ^ (2 * f + 1)) ^ 2 = 2 ^ (4 * f + 2) := by
    rw [← pow_mul]
    congr 1
    ring
  have hlt' : 2 ^ (4 * f + 2) < (fixV (Subgroup.zpowers t)).index := by
    rw [← hpow]
    exact hlt
  have hm := lt_mQuot_of_two_pow_lt_index hW t hlt'
  omega

end CFSG.LocalAnalysis.WeakClosure81
