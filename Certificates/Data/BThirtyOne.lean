module

public import Certificates.Data.CFSGNative.MonsterB.Primes
public meta import Certificates.Data.CFSGNative.MonsterB.Primes

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.SporBig.BThirtyOneNative

open CFSG.Monster.B.Bin CFSG.Monster.B.Primes.Native

set_option compiler.extract_closed false

@[expose] def bThirtyOneProg (_ : Unit := ()) : List Ins :=
  [.mu 1 2 1, .mu 1 2 3, .mu 1 3 4, .mu 1 4 4, .mu 4 4 4, .mu 4 4 5, .mu 4 5 4, .mu 5 4 4,
    .mu 3 3 5, .mu 5 5 5, .mu 5 5 6, .mu 6 6 6, .mu 3 6 3, .mu 5 3 5, .mu 3 5 5, .mu 5 2 2,
    .mu 2 3 2, .mu 1 1 3, .mu 1 3 3, .mu 3 3 3, .mu 3 3 3, .mu 1 3 3, .mu 1 3 1, .mu 1 1 5,
    .mu 1 5 1, .mu 1 4 1, .mu 1 3 1, .mu 1 2 3, .mu 3 2 4, .mu 2 3 5, .mu 1 5 6, .pwr 2 2 2,
    .mu 2 1 7, .mu 7 2 2, .mu 1 2 1, .mu 1 6 1, .pwr 4 1 1, .mu 5 1 1, .mu 4 3 2, .mu 3 4 5,
    .pwr 5 2 2, .pwr 5 5 5, .mu 2 5 2, .mu 3 3 5, .mu 5 5 6, .mu 5 6 7, .mu 4 4 8, .mu 8 8 9,
    .mu 6 8 8, .mu 3 8 10, .mu 3 9 3, .mu 6 7 6, .mu 5 6 5, .mu 10 3 3, .mu 8 4 8, .mu 9 8 8,
    .mu 5 8 5, .pwr 10 4 4, .mu 6 4 4, .mu 4 7 4, .pwr 7 5 5, .pwr 3 2 6, .mu 6 1 7, .pwr 4 1 8,
    .mu 8 6 9, .mu 6 8 6, .mu 2 6 6, .mu 8 8 8, .mu 2 1 1, .mu 1 8 8, .mu 2 6 2, .pwr 4 7 7,
    .pwr 6 1 1, .mu 2 9 2, .mu 8 6 6, .mu 6 2 2, .pwr 2 1 6, .mu 7 6 6, .mu 7 1 1, .mu 6 1 1,
    .mu 1 2 1, .mu 5 1 1, .mu 1 4 1, .pwr 3 1 2]

end CFSG.LocalAnalysis.AGL81I.Section3.SporBig.BThirtyOneNative
