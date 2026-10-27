module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2ExcCommon
public import CFSG.Quasithin.Background.SmithB42D4Main
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2D4LongGen
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2D4Transfer
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Gen
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
import CFSG.Quasithin.Background.F9G2
import CFSG.Quasithin.Background.F9Geometry
import CFSG.Quasithin.Background.SmithB45TorCrit

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

private theorem w183_classA_hnab_of_ctx (hctx : Is135Context Y L) :
    ∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a := by
  have hq : IsQuasisimple ↥L := hctx.2.2.2.2.1
  obtain ⟨x, y, hxy⟩ := hq.2.2
  obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
  refine ⟨x', x'.2, y', y'.2, fun h => hxy ?_⟩
  have hL : (x' * y' : ↥L) = y' * x' := Subtype.ext h
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hL]

private theorem w183_classA_ne_bot_of_ctx (hctx : Is135Context Y L) : L ≠ ⊥ := by
  intro hbot
  obtain ⟨a, ha, b, hb, hab⟩ := w183_classA_hnab_of_ctx hctx
  rw [hbot] at ha hb
  rw [Subgroup.mem_bot.mp ha, Subgroup.mem_bot.mp hb] at hab
  exact hab rfl

include hf hK hσ in
theorem w135c2_trialityD4_classA (hW : ∀ w : W, w ^ 2 = 1) (hctx : Is135Context Y L)
    (hZL : Subgroup.center ↥L = ⊥) (hrk : 24 * f ≤ rk W) {x : ↥L}
    (hx : ConjC σ ((modelProj L e x : C₀) : ModGL TwistTag.D4.tag K) (Xr d4H 1)) :
    4 ≤ E3.mQuot ⊤ (fixV (Subgroup.zpowers (x : MulAut W))) := by
  classical
  have hσ3 : σ.toRingHom ^ 3 = 1 := sigma_cube hK σ hσ
  haveI : CharP K 2 := charP_two_of_card hf hK
  have hHmem : Xr d4H 1 ∈ C₀ := Xr_H_mem_C0 σ hσ3 (map_one σ)
  let ξ : ↥C₀ := ⟨Xr d4H 1, hHmem⟩
  obtain ⟨T, hTc, hTconj, hTgen⟩ := trialityLongRoot_gen hf hK σ hσ
  have hTmem : ∀ y ∈ T, y ∈ C₀ := by
    intro y hy
    obtain ⟨g, hg, hgy⟩ := hTconj y hy
    rw [← hgy]
    exact mul_mem (mul_mem hg hHmem) (inv_mem hg)
  obtain ⟨T', hT'c, hT'mem, hT'gen⟩ := exists_finset_closure_top C₀ T hTmem hTgen
  have hT'conj : ∀ y ∈ T', ∃ g : ↥C₀, y = g * ξ * g⁻¹ := by
    intro y hy
    obtain ⟨g, hg, hgy⟩ := hTconj (y : ModGL TwistTag.D4.tag K) (hT'mem y hy)
    refine ⟨⟨g, hg⟩, Subtype.ext ?_⟩
    change (y : ModGL TwistTag.D4.tag K) = g * Xr d4H 1 * g⁻¹
    exact hgy.symm
  have hxg : ∃ g : ↥C₀, g * modelProj L e x * g⁻¹ = ξ := by
    obtain ⟨g, hg, hgx⟩ := hx
    refine ⟨⟨g, hg⟩, Subtype.ext ?_⟩
    change g * ((modelProj L e x : ↥C₀) : ModGL TwistTag.D4.tag K) * g⁻¹ = Xr d4H 1
    exact hgx
  obtain ⟨T'', hT''c, hT''conj, hT''gen⟩ :=
    exists_conj_gen_of_modelProj L hZL e hxg hT'conj hT'gen
  have hirr : IsIrrOn L ⊤ ⊥ := hctx.2.2.2.2.2
  have hL : L ≠ ⊥ := w183_classA_ne_bot_of_ctx hctx
  have hgen : rk W ≤ 7 * f * E3.mQuot ⊤ (fixV (Subgroup.zpowers (x : MulAut W))) :=
    w135c2_rk_le_mul_of_conj_gen hW hirr hL T'' hT''conj hT''gen (A := 7 * f)
      (hT''c.trans (hT'c.trans hTc))
  by_contra h4
  have hm3 : E3.mQuot ⊤ (fixV (Subgroup.zpowers (x : MulAut W))) ≤ 3 := by omega
  have hle : rk W ≤ 7 * f * 3 :=
    calc rk W ≤ 7 * f * E3.mQuot ⊤ (fixV (Subgroup.zpowers (x : MulAut W))) := hgen
      _ ≤ 7 * f * 3 := Nat.mul_le_mul_left _ hm3
  omega

end CFSG.LocalAnalysis.WeakClosure81
