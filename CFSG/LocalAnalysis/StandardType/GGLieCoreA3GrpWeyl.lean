module

public import CFSG.LocalAnalysis.StandardType.GGLieCoreA3LatticeE6Defs
public import CFSG.LocalAnalysis.StandardType.GGLieCoreA3DictPhi
public import CFSG.HardMathSupport.Timmesfeld.Torality.LangAssembly
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl
public import CFSG.LieType.SeitzGeneration.ExcHighThree.KillsRootGroup
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Frames
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralE7
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralE8
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Core
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Plane
public import CFSG.LieType.Chevalley.ParabolicRadicalNormalizer
public import CFSG.LieType.Chevalley.ParabolicRadicalsOpposite
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcBruhat
public import CFSG.RankThree.Chevalley.SteinbergBNNoninnerComponentNodes
public import CFSG.RankThree.Chevalley.SteinbergCFOddE7E8NoninnerComponent
public import CFSG.RankThree.Lattice.SteinbergBIE6OrderThreeTools
public import CFSG.RankThree.PartOne.KE.Basic
public import CFSG.RankThree.PartOne.KE.E6FourPlane
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KE.E7FourPlane
public import CFSG.RankThree.PartOne.KE.E8NineData
public import CFSG.RankThree.PartOne.KE.NativeCyclicMain
public import CFSG.RankThree.PartOne.KE.PlaneToral
public import CFSG.RankThree.PartOne.KGD.D4QA1

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Torality
open CFSG.Open (StatedLieTag)
open CFSG.LieType.Steinberg.Adjoint (iform)

theorem ggLie_canonicalRep_mul
    (x y : WeylGroup (langTag .E6)) :
    canonicalRep (coxeterSystem (langTag .E6)) GGL (x * y) =
      canonicalRep (coxeterSystem (langTag .E6)) GGL x *
        canonicalRep (coxeterSystem (langTag .E6)) GGL y := by
  exact CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_mul_of_charTwo x y

theorem ggLie_lang_step
    (a : Fin 2 → Fin (langTag .E6).rank → GGLˣ) (u x : WeylGroup (langTag .E6))
    (hu : u ∈ Subgroup.closure (rootReflection '' familyKernel a))
    (hx : (fun α => x • α) '' familyKernel a = familyKernel a)
    (g : ModGL (langTag .E6) GGL)
    (hlang : ggPhi .E6 1 g = g * canonicalRep (coxeterSystem (langTag .E6)) GGL (u * x)) :
    ∃ z ∈ familyGroup (K := GGL) a,
      ggPhi .E6 1 (g * z) = g * z * canonicalRep (coxeterSystem (langTag .E6)) GGL x := by
  have hFeq : entrywiseFrobGL (langTag .E6) GGL 2 1 = ggPhi .E6 1 := rfl
  have hm : canonicalRep (coxeterSystem (langTag .E6)) GGL u ∈ familyGroup (K := GGL) a :=
    CFSG.LieType.SeitzGeneration.ExcHighThree.canonicalRep_closure_mem_familyGroup a hu
  have hQ : canonicalRep (coxeterSystem (langTag .E6)) GGL x ∈
      Subgroup.normalizer (familyGroup (K := GGL) a : Set (ModGL (langTag .E6) GGL)) :=
    canonicalRep_mem_normalizer_of_image (K := GGL) (a := a) (w := x) hx
  have hn : g⁻¹ * ggPhi .E6 1 g =
      canonicalRep (coxeterSystem (langTag .E6)) GGL u *
        canonicalRep (coxeterSystem (langTag .E6)) GGL x := by
    rw [hlang, ggLie_canonicalRep_mul u x]
    group
  have hLang : ∀ c ∈ familyGroup (K := GGL) a,
      ∃ z ∈ familyGroup (K := GGL) a,
        z⁻¹ * (canonicalRep (coxeterSystem (langTag .E6)) GGL x * ggPhi .E6 1 z *
          (canonicalRep (coxeterSystem (langTag .E6)) GGL x)⁻¹) = c := by
    intro c hc
    obtain ⟨z, hz, hzc⟩ :=
      lang_familyGroup (ℓ := 2) a 1 le_rfl
        (canonicalRep (coxeterSystem (langTag .E6)) GGL x) hQ c hc
    exact ⟨z, hz, by simpa [hFeq] using hzc⟩
  obtain ⟨z, hz, hres⟩ := exists_mem_lang_conj (ggPhi .E6 1) hm hn hLang
  refine ⟨z, hz, ?_⟩
  calc ggPhi .E6 1 (g * z) = (g * z) * ((g * z)⁻¹ * ggPhi .E6 1 (g * z)) := by
        rw [mul_inv_cancel_left]
    _ = (g * z) * canonicalRep (coxeterSystem (langTag .E6)) GGL x := by rw [hres]

end CFSG.StandardType.LieCore
