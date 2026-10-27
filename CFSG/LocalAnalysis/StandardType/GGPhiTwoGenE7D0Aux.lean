module

public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenE7Defs
public import CFSG.LieType.SeitzGeneration.ExcHigh.E7FrameTorus
public import CFSG.LieType.Chevalley.E7SupportedBruhat
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhatDefs
public import CFSG.ClassicalInvolution.RouteD.GapsOrthChain
public import CFSG.HardMathSupport.Lang.AnisoE8.D8Planes
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Assembly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerTorus
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.SeitzGeneration.ExcHigh.E7TwoSevenDescent
public import CFSG.Quasithin.Background.G11Stmts
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.Chevalley.SteinbergBNNoninnerComponentNodes
public import CFSG.RankThree.Chevalley.SteinbergCFOddE7E8NoninnerComponent
public import CFSG.RankThree.Lattice.SteinbergBIE6OrderThreeTools
public import CFSG.RankThree.PartOne.K133H.G2Plane
public import CFSG.RankThree.PartOne.KE.Basic
public import CFSG.RankThree.PartOne.KE.E6FourPlane
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KE.E7FourPlane
public import CFSG.RankThree.PartOne.KE.E8NineData
public import CFSG.RankThree.PartOne.KE.NativeCyclicMain
public import CFSG.RankThree.PartOne.KE.PlaneToral
public import CFSG.RankThree.PartOne.KGD.D4QA1

public section

namespace CFSG.StandardType.PhiTwoRootGen

open CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.SeitzGeneration.ExcHigh
  CFSG.StandardType.TableBExcTwo CFSG.RankThree.Chevalley

private lemma e7A1D6Roots_neg_mem {α : Fin (Tag.rank .E7) → ℤ} (hα : α ∈ e7A1D6Roots) :
    -α ∈ e7A1D6Roots := by
  rcases hα with ⟨hroot, hev⟩
  exact ⟨IsRoot.neg hroot, by simpa using hev⟩

private lemma frameE7Root_mem_e7A1D6Roots (i : Fin 7) :
    frameE7Root i ∈ e7A1D6Roots := by
  rw [e7A1D6Roots]
  refine ⟨e7Frame_isRoot i, ?_⟩
  fin_cases i <;> decide +kernel

theorem ggPhiTwoD0_frameSpan_le_rootSpan {L : Type} [Field L] :
    frameSpan L ≤ rootSpan .E7 L e7A1D6Roots := by
  rw [frameSpan]
  refine iSup_le fun i => ?_
  rw [range_rootSL2_of_isRoot (e7Frame_isRoot i)]
  exact sup_le
    (rootSubgroup_le_rootSpan (frameE7Root_mem_e7A1D6Roots i))
    (rootSubgroup_le_rootSpan (e7A1D6Roots_neg_mem (frameE7Root_mem_e7A1D6Roots i)))

theorem ggPhiTwoD0_torus_le_rootSpan {L : Type} [Field L]
    (hsq : ∀ x : L, ∃ z : L, z ^ 2 = x) :
    torusGroup .E7 L ≤ rootSpan .E7 L e7A1D6Roots :=
  (torusGroup_le_frameSpan (L := L) hsq).trans ggPhiTwoD0_frameSpan_le_rootSpan

end CFSG.StandardType.PhiTwoRootGen

end
