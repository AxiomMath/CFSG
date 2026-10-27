module

public import CFSG.Monster.B.Fischer.PinnedChain
public meta import CFSG.Monster.B.Fischer.PinnedChain

public section

namespace CFSG.Monster.B.Fischer

open CFSG.Monster.B.Co2.Native

@[expose] def pinWord (k : ℕ) : List ℤ := ((pinMembership[k]?).map (·.strongGeneratorWord)).getD []

end CFSG.Monster.B.Fischer
