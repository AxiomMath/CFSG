module

public import Certificates.Data.CFSGNative.Timmesfeld.Fi24Cl
public meta import Certificates.Data.CFSGNative.Timmesfeld.Fi24Cl

public section

namespace Timmesfeld.Fi24Cl

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Fi24.Native

set_option compiler.extract_closed false

@[expose] def fixCount24 (T : Table) : Nat :=
  ((List.range 306936).filter fun i => ap T i == i).length

@[expose] def repFixData : List (List Nat × Nat) :=
  [([18], 3240), ([16, 19], 1485), ([14, 16, 16, 14, 16, 16], 378), ([16], 162), ([2], 0)]

@[expose] def fi24RepFixOK (O : Enum) : Bool :=
  let letters := chainLetters O
  repFixData.all fun d => fixCount24 (wordTable letters d.1) == d.2

end Timmesfeld.Fi24Cl
