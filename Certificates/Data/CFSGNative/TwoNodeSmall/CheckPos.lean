module

public import Certificates.Data.CFSGNative.TwoNodeSmall.SearchPos

public section

namespace CFSG.TwoNodeSmall

set_option compiler.extract_closed false

@[expose] def check1Pos (Q : SPt) : Bool :=
  match findPos Q with
  | some w => verifyPos Q w
  | none => false

@[expose] def check1Excl (Q : SPt) : Bool :=
  match findExcl Q with
  | some w => verifyExcl Q w
  | none => false

@[expose] def posBCheck (_ : Unit := ()) : Bool := (posBPts ()).all check1Pos

@[expose] def exclCheck (_ : Unit := ()) : Bool := (exclPts ()).all check1Excl

end CFSG.TwoNodeSmall
