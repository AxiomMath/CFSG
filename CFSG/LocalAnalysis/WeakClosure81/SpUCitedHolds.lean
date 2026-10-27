module

public import CFSG.LocalAnalysis.WeakClosure81.SpUCitedOut
public import CFSG.LocalAnalysis.WeakClosure81.SpUCitedParSpHolds
public import CFSG.LocalAnalysis.WeakClosure81.SpUCitedParUHolds
public import CFSG.LocalAnalysis.WeakClosure81.SpUFixFactHolds

public section

namespace CFSG.LocalAnalysis.WeakClosure81

theorem spPSUParabolicFact_holds : SpPSUParabolicFact :=
  fun _ _ _ _ _ _ _ =>
    ⟨fun h => spUCited_parabolic_of_spRootSetup h, fun h => uCited_parabolic_of_psuRootSetup h⟩

theorem spPSULieFacts_holds : SpPSULieFacts :=
  spPSULieFacts_of_cited spPSUOutFact_holds spPSUParabolicFact_holds

end CFSG.LocalAnalysis.WeakClosure81

end
