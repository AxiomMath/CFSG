module

public import CFSG.LocalAnalysis.StandardType.GGExcKGSFTrRF
public import CFSG.LocalAnalysis.StandardType.GGExcKGSFTrF5W
public import CFSG.LocalAnalysis.StandardType.GGExcKGSFTrComp
public import CFSG.LocalAnalysis.StandardType.GGExcKGSFTrClauseA
public import CFSG.LocalAnalysis.StandardType.GGExcKGSFTrExists
public import CFSG.LocalAnalysis.StandardType.GGExcKGSFOutput

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank

section Universal

theorem ggExcKGSFOutput_of_model (hCI : GGKGInndiagCI) (Mod : GGModelFamily)
    (hComp : GGModelComp Mod) : GGExcKGSFOutput := by
  intro t n f ht G _ _ ψ hset p hp hp2 hreg Bs hBs h4 hN hdiag hP
  obtain ⟨T⟩ := exists_ggSFTr hCI ht hset hp hp2 hreg (Mod t n f ht hset.1 p hp hp2 hreg) hBs h4
    hN hdiag hP
  obtain ⟨hcomp, hA, hAU⟩ := hComp t n f ht hset.1 p hp hp2 hreg
  exact ⟨_, _, ⟨T.coord, T.coord_inj, T.coord_fixed, T.coord_surj, (T.comp hcomp).1,
    (T.comp hcomp).2⟩, (Mod t n f ht hset.1 p hp hp2 hreg).hS,
    (Mod t n f ht hset.1 p hp hp2 hreg).hπ, T.rf, T.f5, T.w, T.clauseA hA, T.clauseAU hAU⟩

end Universal

end CFSG.StandardType
