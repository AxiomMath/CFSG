module

public import CFSG.Sporadic.HNSchreier.FALocal

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier

@[expose] def iGen (k : ℕ) : JH := if k < 5 then aGenJ k else commJ

@[expose] def a6Gen (k : ℕ) : JH := hWordJ FAData.a6Words[k]!

end CFSG.Sporadic.HNOddCore
