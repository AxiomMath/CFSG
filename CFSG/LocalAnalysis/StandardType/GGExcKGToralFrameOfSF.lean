module

public import CFSG.LocalAnalysis.StandardType.GGExcKGSFOutput

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.LieType.AschbacherSeitz

section FullCerts

theorem ggExcKGToralFrame_of_sfOutput (h : GGExcKGSFOutput) : GGExcKGToralFrame := by
  intro t n f ht G _ _ ψ hset p hp hp2 hreg Bs hBs hcard hN hdiag hP
  obtain ⟨S, π, F, hS, hπ, hRF, hF5, hW, hA, hAU⟩ :=
    h t n f ht G ψ hset p hp hp2 hreg Bs hBs hcard hN hdiag hP
  exact ⟨S, π, F, ⟨hS, hπ.1, hπ.2.1, hπ.2.2.1, hπ.2.2.2,
    f3_of_rankOneFrame_of_central t ht n f hset.1.1.2.1 ψ hset.2.1 p Bs S π F hRF, hF5⟩,
    hW, hA, hAU⟩

end FullCerts

end CFSG.StandardType
