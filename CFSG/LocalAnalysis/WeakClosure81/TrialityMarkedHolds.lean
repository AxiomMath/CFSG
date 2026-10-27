module

public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenTriDefs
import CFSG.LocalAnalysis.WeakClosure81.TrialityMarkedT
import CFSG.LocalAnalysis.WeakClosure81.TrialityMarkedG1

public section

namespace CFSG.LocalAnalysis.WeakClosure81

theorem trialityMarkedInput_holds : TrialityMarkedInput := fun _ _ _ ⟨ε, h⟩ =>
  ⟨ε, h.surjective, h.isSwap, h.centralizer_eq_closure, h.exists_line⟩

end CFSG.LocalAnalysis.WeakClosure81

end
