module

public import CFSG.Quasithin.Vol2.Ch5AssemblyClause
import CFSG.Quasithin.Vol2.Ch5ModulesOrth
public import CFSG.Quasithin.Vol2.Ch5Assembly

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

theorem ch5KZConclusion
    : Ch5KZConclusion := by
  intro G _ _ T M L V H n _ _ hK _ hV hle hKZ
  exact ⟨hV.commutator, centralizerComponentClause_of_KZ hK hle hKZ⟩

theorem ch5KZConclusionD4 :
    Ch5KZConclusionD4 := by
  intro G _ _ T M L V H n _ _ h
  exact ⟨h.2.2.1.commutator, centralizerComponentClause_of_3D4 h.1 h.2.2.2.1 h.2.2.2.2⟩

theorem ch5L34Conclusion_of
    (h39 : Vol2Native.A39ForSQTKCat) : Ch5L34Conclusion := by
  intro G _ _ T M L V H B D n hyp _ _ hK hc
  refine ⟨?_, centralizerComponentClause_of_L34 h39 hyp hK hc.1.1 hc.2.1.1⟩
  rcases hc.2.2.2.1.2.1 with h | h
  · exact (isA5ModuleSum_of_s5 h.2 hyp.commutator_eq hyp.sylow.1 hyp.T_le_normalizer).commutator
  · exact h.isA5ModuleSum_commutator

end CFSG.Quasithin.H13
