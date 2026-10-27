module

public import Certificates.Data.CFSGNative.AS91.M24Geom

public section

namespace CFSG.KC.M24G

open CFSG.Quasithin.H13.AS91.M24G

@[expose] def tsRowOK (SL : List (List Nat)) (t : Nat × Nat × Nat) (r : List Nat) : Bool :=
  r.length == 7 && decide (r.Pairwise (· < ·)) &&
    r.all fun q => decide (q < 1771) && Native.trioIn t (SL.getD q default)

@[expose] def tsRowsOK (TL : List (Nat × Nat × Nat)) (SL : List (List Nat))
    (TS : List (List Nat)) : Bool :=
  TL.length == 3795 && TS.length == 3795 && (TL.zip TS).all fun x => tsRowOK SL x.1 x.2

end CFSG.KC.M24G
