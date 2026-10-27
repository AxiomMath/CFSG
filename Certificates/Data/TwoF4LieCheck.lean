module

public import Certificates.Data.RuF45Geom
public import Certificates.Data.TwoF4LieData

public section

namespace CFSG.TwoF4Lie

open CFSG.Monster.B.Co2.Native CFSG.RuF45

@[expose] def wordOK (s : String) : Bool := (decodeWord s).all fun l => decide (l.1 < 4)

@[expose] def wArr (G Gi : Array (Array Nat)) (s : String) : Array Nat :=
  evalArr 1755 G Gi (decodeWord s)

@[expose] def fixesH (pts g : Array Nat) : Bool := actOK pts g 0 0

@[expose] def fixesN (pts g : Array Nat) : Bool := actOK pts g 1755 1755

@[expose] def fixesS (pts g : Array Nat) : Bool := fixesH pts g && fixesN pts g

@[expose] def tArr (G Gi : Array (Array Nat)) : Array Nat := wArr G Gi tWord

@[expose] def cArr (G Gi : Array (Array Nat)) : Array Nat := wArr G Gi cWord

end CFSG.TwoF4Lie
