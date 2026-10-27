module

public import CFSG.Quasithin.Recognition.Kleidman.ThreeLocalCentralizerAnalysis.BetaModels

public section

namespace CFSG.Quasithin.Kleidman.ThreeLocal

open Matrix MatrixGroups

@[expose] def c0L3 : SL(3, ZMod 2) := ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide⟩

set_option maxRecDepth 100000 in
theorem betaCheck_L3 : BetaCheck SL(3, ZMod 2) c0L3 := by
  decide +kernel

end CFSG.Quasithin.Kleidman.ThreeLocal
