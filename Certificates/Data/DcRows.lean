module

public import Certificates.Data.CFSGNative.H13.LocDblDc

public section

namespace CFSG.Quasithin.H13.LocDbl.DcNative

@[expose] def enumRowList (B : List Nat) (G : Array (Array Nat)) (par lab : Array Nat) (N : Nat) :
    List (List Nat) :=
  let P := B.map (ptsArr G par lab N)
  (List.range N).map fun k => P.map fun A => A.getD k 0

end CFSG.Quasithin.H13.LocDbl.DcNative
