module

public import Certificates.Data.CFSGNative.Co2Rank.Dfs
public import CFSG.Sporadic.Co2InvCheckInputs

public section

namespace CFSG.Sporadic.Co2Heavy

open CFSG.Sporadic.Co2Rank CFSG.Sporadic.Co2Inv CFSG.Sporadic.SmallF2.Native
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Co2Cert

set_option compiler.extract_closed false

@[expose] def hRow (k : ℕ) : Array ℕ := enumS.elems[k]!

end CFSG.Sporadic.Co2Heavy
