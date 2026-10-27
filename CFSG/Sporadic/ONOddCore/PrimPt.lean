module

public import CFSG.Sporadic.ONOddCore.PrimCheckInputs
public import CFSG.Sporadic.Schreier.ONVectorData

public section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier

theorem primReps_lt {i : ℕ} (hi : i < 5) : primReps.getD i 0 < nL := by
  interval_cases i <;> decide

@[expose] def primPt {i : ℕ} (hi : i < 5) : Fin nL := ⟨primReps.getD i 0, primReps_lt hi⟩

end CFSG.Sporadic.ONOddCore

end
