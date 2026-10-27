module

public import CFSG.LocalAnalysis.StandardType.GGLangAssemblyComp
public import CFSG.LocalAnalysis.StandardType.GGLangAssemblyA
public import CFSG.LocalAnalysis.StandardType.GGLangAssemblyAU

public section

namespace CFSG.StandardType

section Assembly

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal CFSG.LieType.RootSystem
open CFSG.Open CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

theorem ggModelComp_of_langData
    (L : Type) [Field L] [IsAlgClosed L] [Algebra (ZMod 2) L] [Algebra.IsAlgebraic (ZMod 2) L]
    (Mod : GGModelFamily) (hdata : GGModelLangData L Mod)
    (hZ : LangRat.LangRatCentralizerDetectsP) : GGModelComp Mod := by
  intro t n f ht hadm p hp hp2 hreg
  obtain ⟨B⟩ := hdata t n f ht hadm p hp hp2 hreg
  exact ⟨ggClauseComp_of_langData hp hp2 B hZ, ggClauseA_of_langData hp hp2 B hZ,
    ggClauseAU_of_langData hp hp2 B⟩

theorem ggModelCompInput_of_langData
    (L : Type) [Field L] [IsAlgClosed L] [Algebra (ZMod 2) L] [Algebra.IsAlgebraic (ZMod 2) L]
    (Mod : GGModelFamily) (hdata : GGModelLangData L Mod)
    (hZ : LangRat.LangRatCentralizerDetectsP) : GGModelCompInput :=
  ⟨Mod, ggModelComp_of_langData L Mod hdata hZ⟩

end Assembly

end CFSG.StandardType
