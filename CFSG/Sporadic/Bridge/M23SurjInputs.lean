module

public import Certificates.Data.CFSGNative.Bridge.SurjA
public import CFSG.Sporadic.Mathieu.Simple
public import CFSG.Sporadic.Schreier.M23Base
public import CFSG.Sporadic.Schreier.Outer

public section

namespace CFSG.Sporadic.Bridge.M23

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Bridge.TwoGen
  CFSG.Sporadic.Bridge.TwoGen.Native TauCeti
open CFSG.Sporadic.Schreier (m23GenA m23GenB m23_eq_closure m23_card)
open CFSG.Sporadic.Mathieu (closure_pair_eq_top)

@[expose] def tabA : Table :=
  #[1, 0, 3, 2, 4, 5, 7, 6, 9, 8, 10, 11, 13, 12, 15, 14, 16, 17, 19, 18, 21, 20, 22]

@[expose] def tabB : Table :=
  #[15, 8, 0, 4, 7, 21, 6, 22, 20, 9, 2, 1, 19, 17, 16, 10, 14, 5, 18, 12, 11, 13, 3]

@[expose] def tabBi : Table :=
  #[2, 11, 10, 22, 3, 17, 6, 4, 1, 9, 15, 20, 19, 21, 16, 0, 14, 13, 18, 12, 8, 5, 7]

end CFSG.Sporadic.Bridge.M23
