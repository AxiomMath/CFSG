module

public import CFSG.Sporadic.Co2Smith.CCNative
public import CFSG.Sporadic.Co2Smith.CRep

public section

namespace CFSG.Sporadic.Co2Smith

@[expose] noncomputable def cR
    (i : ℕ) : Cz := cE (Native.ccReps[i]!).1 (Native.ccReps[i]!).2

theorem ccReps_snd_lt {i : ℕ} (hi : i < 9) : (Native.ccReps[i]!).2 < 1451520 := by
  interval_cases i <;> decide

end CFSG.Sporadic.Co2Smith
