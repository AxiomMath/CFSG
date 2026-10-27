module

public import CFSG.LocalAnalysis.OddStandard.Solomon75AhatDataInputs

public section

namespace Certificates.Solomon75Sec5Q

open CFSG.OddStandard.Solomon75.AhatData

@[expose] def sigA (n : Nat) : Array Nat := swapsA n [(0, 1), (2, 3), (4, 5), (6, 7)]

@[expose] def cardC (n : Nat) : Nat :=
  if n = 8 then 384 else if n = 9 then 384 else if n = 10 then 768 else 2304

end Certificates.Solomon75Sec5Q
