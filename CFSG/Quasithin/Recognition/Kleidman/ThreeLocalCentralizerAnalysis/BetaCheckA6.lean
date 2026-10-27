module

public import CFSG.Quasithin.Recognition.Kleidman.ThreeLocalCentralizerAnalysis.BetaModels
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.Quasithin.Kleidman.ThreeLocal

@[expose] def c0A6 : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

set_option maxRecDepth 100000 in
theorem betaCheck_A6 : BetaCheck (alternatingGroup (Fin 6)) c0A6 := by
  decide +kernel

end CFSG.Quasithin.Kleidman.ThreeLocal
