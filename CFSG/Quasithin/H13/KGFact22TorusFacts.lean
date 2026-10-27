module

public import CFSG.Quasithin.H13.KGFact22TorL2
public import CFSG.Quasithin.H13.KGFact22TorSp
public import CFSG.Quasithin.H13.KGFact22TorU3
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalBender
public import CFSG.StronglyEmbedded.ParityCriterion

public section

namespace CFSG.Quasithin.H13

open KG22 in
theorem e22TorusFacts_holds : E2.E22TorusFacts := by
  intro X _ _ n hn hX S hS
  rcases hX with ⟨-, hL2 | hSz | hU3⟩ | hL3 | hSp
  · exact torusOut_of_isPSL2 (by omega) hL2 hS
  · exact torusOut_of_isSz hSz hS
  · exact torusOut_of_isPSU3 hn hU3 hS
  · exact torusOut_of_isPSL3 (by omega) hL3 hS
  · exact torusOut_of_isPSp4 (by omega) hSp hS

end CFSG.Quasithin.H13
