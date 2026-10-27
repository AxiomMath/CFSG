module

public import CFSG.Sporadic.Mathieu.M24
public import Certificates.Data.CFSGNative.Bridge.SurjA
public import TauCeti.GroupTheory.Presentation.Relator

public section

namespace CFSG.Sporadic.Bridge.M24

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Bridge.TwoGen
  CFSG.Sporadic.Bridge.TwoGen.Native TauCeti
open CFSG.Sporadic.Mathieu (m24a m24b rep_m24a rep_m24b m24_eq card_M24 closure_pair_eq_top)
open CFSG.Sporadic.Mathieu.Native (m24Data)

@[expose] def tabBi : Table :=
  #[5, 13, 14, 0, 9, 3, 6, 7, 2, 17, 10, 11, 15, 20, 8, 16, 12, 4, 22, 19, 1, 21, 23, 18]

end CFSG.Sporadic.Bridge.M24
